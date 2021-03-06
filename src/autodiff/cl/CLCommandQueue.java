package autodiff.cl;

import static org.jocl.CL.clCreateCommandQueue;
import static org.jocl.CL.clEnqueueNDRangeKernel;
import static org.jocl.CL.clEnqueueReadBuffer;
import static org.jocl.CL.clReleaseCommandQueue;

import java.io.Serializable;

import org.jocl.CL;
import org.jocl.Pointer;
import org.jocl.Sizeof;
import org.jocl.cl_command_queue;
import org.jocl.cl_mem;

/**
 * @author codistmonk (creation 2014-12-02)
 */
public final class CLCommandQueue implements Serializable {
	
	private final cl_command_queue commandQueue;
	
	public CLCommandQueue(final CLContext context) {
		this.commandQueue = clCreateCommandQueue(context.getContext(), context.getDevice().getId(), 0, null);
	}
	
	public final cl_command_queue getCommandQueue() {
		return this.commandQueue;
	}
	
	public final void enqueueNDRangeKernel(final CLKernel kernel,
			final long[] globalWorkSize, final long[] localWorkSize) {
		clEnqueueNDRangeKernel(this.getCommandQueue(), kernel.getKernel(), globalWorkSize.length, null,
				globalWorkSize, localWorkSize, 0, null, null);
	}
	
	public final void enqueueReadBuffer(final boolean blocking, final cl_mem buffer, final float[] result) {
		this.enqueueReadBuffer(blocking, buffer, Sizeof.cl_float * result.length, Pointer.to(result));
	}
	
	public final void enqueueWriteBuffer(final boolean blocking, final cl_mem buffer, final float[] values) {
		this.enqueueWriteBuffer(blocking, buffer, Sizeof.cl_float * values.length, Pointer.to(values));
	}
	
	public final void enqueueWriteBuffer(final boolean blocking, final cl_mem buffer, final long bytes, final Pointer result) {
		CL.clEnqueueWriteBuffer(this.getCommandQueue(), buffer, blocking, 0,
				bytes, result, 0, null, null);
	}
	
	public final void enqueueReadBuffer(final boolean blocking, final cl_mem buffer, final long bytes, final Pointer result) {
		clEnqueueReadBuffer(this.getCommandQueue(), buffer, blocking, 0,
				bytes, result, 0, null, null);
	}
	
	public final void release() {
		clReleaseCommandQueue(this.getCommandQueue());
	}
	
	/**
	 * {@value}.
	 */
	private static final long serialVersionUID = -8782273179290708884L;
	
}
