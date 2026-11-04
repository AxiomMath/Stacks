module

public import StacksFrontier.AlgebraicGeometry.TateMap.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleExistence0BVG
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeTraceSection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties

/-!
# The relative dualizing module and the trace section of an object of Section 0FKB

For a locally quasi-finite syntomic morphism `f : Y ⟶ X` with `X` locally Noetherian, the
source is locally Noetherian and `f` is flat and locally of finite type, so `f` has the relative
dualizing module `ω_{Y/X}` of Tag 0BVG and its trace section `τ_{Y/X}` of Tag 0BVJ.

## Main definitions

* `AlgebraicGeometry.TateMap.omegaData`: the chart data of `ω_{Y/X}`, chosen once; any two
  choices are related by the unique comparison of the uniqueness half of Tag 0BVG.
* `AlgebraicGeometry.TateMap.omega`: the `𝒪_Y`-module `ω_{Y/X}`.
* `AlgebraicGeometry.TateMap.tau`: the global section `τ_{Y/X}`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.TateMap

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : Y ⟶ X)

omit [IsLocallyNoetherian X] in
/-- A locally quasi-finite syntomic morphism is locally of finite type. -/
theorem locallyOfFiniteType (hf : IsQuasiFiniteSyntomic f) : LocallyOfFiniteType f :=
  have := AlgebraicGeometry.locallyOfFinitePresentation hf.2
  inferInstance

/-- The source of a locally quasi-finite syntomic morphism with locally Noetherian target is
locally Noetherian. -/
theorem isLocallyNoetherian_source (hf : IsQuasiFiniteSyntomic f) : IsLocallyNoetherian Y :=
  have := locallyOfFiniteType f hf
  LocallyOfFiniteType.isLocallyNoetherian f

/-- The chart data of the relative dualizing module `ω_{Y/X}` of Tag 0BVG. -/
def omegaData (hf : IsQuasiFiniteSyntomic f) :
    letI := isLocallyNoetherian_source f hf
    letI := hf.1
    Stacks.Discriminant.RelativeDualizingModuleData f :=
  letI := isLocallyNoetherian_source f hf
  letI := hf.1
  letI := locallyOfFiniteType f hf
  (Stacks.Discriminant.nonempty_relativeDualizingModuleData f).some

/-- The relative dualizing module `ω_{Y/X}`. -/
abbrev omega (hf : IsQuasiFiniteSyntomic f) : Y.Modules :=
  letI := isLocallyNoetherian_source f hf
  letI := hf.1
  (omegaData f hf).sheaf

/-- The trace section `τ_{Y/X} ∈ Γ(Y, ω_{Y/X})` of Tag 0BVJ. -/
def tau (hf : IsQuasiFiniteSyntomic f) : Γ(omega f hf, ⊤) :=
  letI := isLocallyNoetherian_source f hf
  letI := hf.1
  letI : Flat f := AlgebraicGeometry.flat hf.2
  Stacks.Discriminant.relativeTraceSection (omegaData f hf)

end AlgebraicGeometry.TateMap
