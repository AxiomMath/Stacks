module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Embedding.IsSupported
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# The cohomology of a complex of projectives with projective cohomology commutes with right exact
functors

Let `K^•` be a bounded above cochain complex in an abelian category whose terms and whose
cohomology objects are all projective.  Then the complex splits: every object of opcycles
`Coker(d^{n-1})` is projective, and the map `Coker(d^{n-1}) ⟶ K^{n+1}` induced by the differential
factors as a split epimorphism followed by a split monomorphism.  Consequently every additive
right exact functor `F` commutes with the cohomology of `K^•`:

`H^n(F K^•) ≅ F(H^n(K^•))`.

For modules and `F = - ⊗_R S` this is the statement that cohomology commutes with base change for a
bounded above complex of projective modules with projective cohomology, which is how the ranks of
the cohomology modules of such a complex are computed after base change.

## Main results

* `CategoryTheory.Functor.preservesKernel_of_projective_of_projective_cokernel`: an additive
  functor preserves the kernel of a morphism into a projective object with projective cokernel.
* `HomologicalComplex.projective_opcycles_of_projective`: the opcycles of a bounded above complex
  with projective terms and projective cohomology are projective.
* `HomologicalComplex.mapHomologyIsoOfProjective`: `H^n(F K^•) ≅ F(H^n(K^•))` for an additive right
  exact functor `F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The image of a morphism followed by the projection to its cokernel is short exact. -/
private theorem shortExact_image_ι_cokernel_π {A B : C} (g : A ⟶ B) :
    (ShortComplex.mk (Abelian.image.ι g) (cokernel.π g) (kernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_kernel (cokernel.π g) }

/-- The kernel of a morphism followed by the factorization through its image is short exact. -/
private theorem shortExact_kernel_ι_factorThruImage {A B : C} (g : A ⟶ B) :
    (ShortComplex.mk (kernel.ι g) (Abelian.factorThruImage g) (by
      rw [← cancel_mono (Abelian.image.ι g), Category.assoc, Abelian.image.fac,
        kernel.condition, zero_comp])).ShortExact :=
  { exact := ShortComplex.exact_of_f_is_kernel _ (isKernelOfComp (Abelian.image.ι g) g
      (kernelIsKernel g) _ (Abelian.image.fac g)) }

/-- The image of a morphism into a projective object with projective cokernel is projective: it
is a direct summand of the target. -/
theorem projective_image_of_projective_of_projective_cokernel {A B : C} (g : A ⟶ B)
    [Projective B] [Projective (cokernel g)] : Projective (Abelian.image g) :=
  have hS := shortExact_image_ι_cokernel_π g
  Retract.projective (X := Abelian.image g) (Y := B)
    ⟨Abelian.image.ι g, hS.splittingOfProjective.r, hS.splittingOfProjective.f_r⟩

/-- **An additive functor preserves the kernel of a morphism into a projective object with
projective cokernel.**  The morphism factors as an epimorphism onto its image followed by the
inclusion of the image; both short exact sequences split, the image and the cokernel being
projective, and a split short exact sequence is sent to a split short exact sequence. -/
theorem Functor.preservesKernel_of_projective_of_projective_cokernel (F : C ⥤ D) [F.Additive]
    {A B : C} (g : A ⟶ B) [Projective B] [Projective (cokernel g)] :
    PreservesLimit (parallelPair g 0) F := by
  have := projective_image_of_projective_of_projective_cokernel g
  have := (shortExact_image_ι_cokernel_π g).splittingOfProjective.isSplitMono_f
  have hlim : IsLimit (KernelFork.ofι (F.map (kernel.ι g))
      (by rw [← F.map_comp, kernel.condition, F.map_zero]) : KernelFork (F.map g)) :=
    isKernelCompMono
      (((shortExact_kernel_ι_factorThruImage g).splittingOfProjective.map F).fIsKernel)
      (F.map (Abelian.image.ι g))
      ((F.congr_map (Abelian.image.fac g)).symm.trans (F.map_comp _ _))
  exact preservesLimit_of_preserves_limit_cone (kernelIsKernel g)
    ((isLimitMapConeForkEquiv' F (kernel.condition g)).symm hlim)

end CategoryTheory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (K : CochainComplex C ℤ)

/-- The cokernel of the map `Coker(d^{n-1}) ⟶ K^{n+1}` induced by the differential is the next
object of opcycles `Coker(d^n)`. -/
def cokernelFromOpcyclesIsoOpcyclesNext (n : ℤ) :
    cokernel (K.sc n).fromOpcycles ≅ K.opcycles ((ComplexShape.up ℤ).next n) :=
  (cokernelEpiComp (K.sc n).pOpcycles (K.sc n).fromOpcycles).symm ≪≫
    cokernelIsoOfEq (K.sc n).p_fromOpcycles ≪≫
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (K.d n _))
      (K.opcyclesIsCokernel n ((ComplexShape.up ℤ).next n) (by simp))

/-- The cohomology of a complex in degree `n` is the kernel of the map
`Coker(d^{n-1}) ⟶ K^{n+1}` induced by the differential. -/
def homologyIsoKernelFromOpcycles (n : ℤ) :
    K.homology n ≅ kernel (K.sc n).fromOpcycles :=
  IsLimit.conePointUniqueUpToIso (K.sc n).homologyIsKernel (limit.isLimit _)

/-- **The opcycles of a bounded above complex with projective terms and projective cohomology are
projective.**  Descending from a degree above the bound, `Coker(d^{n-1})` is an extension of the
image of `Coker(d^{n-1}) ⟶ K^{n+1}` — a direct summand of `K^{n+1}` because its cokernel
`Coker(d^n)` is projective — by the cohomology `H^n(K)`, and this extension splits. -/
theorem projective_opcycles_of_projective (b : ℤ) [CochainComplex.IsStrictlyLE K b]
    (hX : ∀ i, Projective (K.X i)) (hH : ∀ i, Projective (K.homology i)) (i : ℤ) :
    Projective (K.opcycles i) := by
  have step : ∀ n : ℤ, Projective (K.opcycles (n + 1)) → Projective (K.opcycles n) := by
    intro n hn
    have : Projective (cokernel (K.sc n).fromOpcycles) :=
      Projective.of_iso (K.cokernelFromOpcyclesIsoOpcyclesNext n).symm (by simpa using hn)
    have : Projective (K.sc n).X₃ := hX _
    have := projective_image_of_projective_of_projective_cokernel (K.sc n).fromOpcycles
    have : Projective (kernel (K.sc n).fromOpcycles) :=
      Projective.of_iso (K.homologyIsoKernelFromOpcycles n) (hH n)
    have hS := shortExact_kernel_ι_factorThruImage (K.sc n).fromOpcycles
    exact Projective.of_iso hS.splittingOfProjective.isoBinaryBiproduct.symm inferInstance
  have hzero : ∀ n : ℤ, b < n → Projective (K.opcycles n) := by
    intro n hn
    have h : IsZero (K.X n) := CochainComplex.isZero_of_isStrictlyLE K b n hn
    exact Projective.of_iso ((K.sc n).opcyclesIsoX₂ (h.eq_of_tgt _ _)).symm
      (Projective.of_iso h.isoZero.symm inferInstance)
  have aux : ∀ m : ℕ, ∀ n : ℤ, b + 1 - n ≤ (m : ℤ) → Projective (K.opcycles n) := by
    intro m
    induction m with
    | zero => exact fun n hn => hzero n (by lia)
    | succ m ih => exact fun n hn => step n (ih (n + 1) (by lia))
  exact aux (b + 1 - i).toNat i (by lia)

/-- **Cohomology of a complex of projectives with projective cohomology commutes with right exact
functors.**  For a bounded above cochain complex `K^•` whose terms and cohomology objects are
projective, and an additive functor `F` preserving finite colimits, `H^n(F K^•) ≅ F(H^n(K^•))`. -/
def mapHomologyIsoOfProjective (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F] (b : ℤ)
    [CochainComplex.IsStrictlyLE K b] (hX : ∀ i, Projective (K.X i))
    (hH : ∀ i, Projective (K.homology i)) (n : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n ≅ F.obj (K.homology n) :=
  haveI hcok : Projective (cokernel (K.sc n).rightHomologyData.g') :=
    Projective.of_iso (K.cokernelFromOpcyclesIsoOpcyclesNext n).symm
      (K.projective_opcycles_of_projective b hX hH _)
  haveI : (K.sc n).rightHomologyData.IsPreservedBy F :=
    { f := inferInstance
      g' := @Functor.preservesKernel_of_projective_of_projective_cokernel _ _ _ _ _ _ F _ _ _
        (K.sc n).rightHomologyData.g' (hX _) hcok }
  haveI : F.PreservesRightHomologyOf (K.sc n) :=
    Functor.PreservesRightHomologyOf.mk' F (K.sc n).rightHomologyData
  (K.sc n).mapHomologyIso' F

end HomologicalComplex

end
