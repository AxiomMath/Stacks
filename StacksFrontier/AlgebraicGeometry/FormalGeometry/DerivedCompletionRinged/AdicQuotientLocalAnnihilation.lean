module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedTensorGlobalSectionLinear
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.NilpotentIdeal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAnnihilation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientReduction

/-!
# The derived reductions modulo the powers of a sheaf of ideals are killed by local sections

Let `(𝒞, 𝒪)` be a ringed site, `ℐ ⊂ 𝒪` a sheaf of ideals, `K ∈ D(𝒪)` and `n ≥ 1`. For a local
section `f ∈ ℐ(U)`, multiplication by `fⁿ` is zero on the restriction of `K ⊗^𝐋_𝒪 𝒪/ℐⁿ` to the
slice site over `U`. Hence `K ⊗^𝐋_𝒪 𝒪/ℐⁿ` is derived complete along `ℐ`: this is the reason
[Stacks, Tag 0CQH] gives, "it is annihilated by powers of local sections of `ℐ`".

## Main definitions

* `AlgebraicGeometry.RingedSite.SectionKills`: a section `a` of `𝒪` over `U` kills a sheaf of
  modules `S` when every restriction of `a` annihilates the sections of `S` there.

## Main results

* `AlgebraicGeometry.RingedSite.SectionKills.of_epi`: killing passes to quotients.
* `AlgebraicGeometry.RingedSite.SectionKills.sheafTensor`: a section killing `N` kills `S ⊗_𝒪 N`.
* `AlgebraicGeometry.RingedSite.sectionKills_pow_adicQuotientModule`: `fⁿ` kills `𝒪/ℐⁿ` for
  `f ∈ ℐ(U)`.
* `AlgebraicGeometry.RingedSite.smul_id_overFunctor_derivedTensor_adicQuotientObj_eq_zero`:
  `fⁿ` acts as zero on `(K ⊗^𝐋_𝒪 𝒪/ℐⁿ)|_U`.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_derivedTensor_adicQuotient`: `K ⊗^𝐋_𝒪 𝒪/ℐⁿ`
  is derived complete along `ℐ`, for every sheaf of ideals `ℐ` and every `n ≥ 1`.

## Implementation notes

A local section `f ∈ ℐ(U)` is not a global endomorphism of `Mod(𝒪)`, so the linearity of the
derived tensor product over global sections cannot be applied to it directly. The argument
instead works on a representative: `K` is the class of a K-flat complex `P`, and on a K-flat
left factor the derived tensor product is the total tensor complex
`Tot(P ⊗_𝒪 𝒪/ℐⁿ[0])`, whose degree-`i` term is `Pⁱ ⊗_𝒪 𝒪/ℐⁿ` (the other summands vanish).
That sheaf is killed by `fⁿ` sectionwise over every object over `U`: a section of a tensor
product sheaf is locally a sum of pure tensors, and `fⁿ` kills the right factor. Restriction to
the slice is exact, so it computes the restriction of the derived object degreewise, and the
action of `fⁿ` there is zero already on the complex.

No hypothesis on `ℐ` is used: not finite type, not global generation.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 0CQH](https://stacks.math.columbia.edu/tag/0CQH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u})

/-- The structure sheaf restricted to a slice is a sheaf of commutative rings. -/
theorem isMulCommutative_tensorRingSheaf_over (U : X.C) (V : (Over U)ᵒᵖ) :
    IsMulCommutative (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).obj.obj V) := by
  show IsMulCommutative (X.O.obj.obj (op V.unop.left))
  infer_instance

attribute [local instance] isMulCommutative_tensorRingSheaf_over

section Sections

/-- A section `a` of `𝒪` over `U` *kills* a sheaf of modules `S` when, for every object `W`
mapping to `U`, the restriction of `a` to `W` annihilates every section of `S` over `W`. -/
def SectionKills {U : X.Cᵒᵖ} (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
    (S : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) : Prop :=
  ∀ ⦃W : X.Cᵒᵖ⦄ (g : U ⟶ W) (y : S.val.obj W),
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g a • y = 0

variable {X}

namespace SectionKills

variable {U : X.Cᵒᵖ} {a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U}

/-- The restrictions of a killing section kill. -/
theorem map {S : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : SectionKills X a S) {V : X.Cᵒᵖ} (g : U ⟶ V) :
    SectionKills X ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g a) S := by
  intro W k y
  rw [← RingCat.comp_apply, ← Functor.map_comp]
  exact h (g ≫ k) y

/-- **Killing passes to quotients.** A section of the target of an epimorphism is locally a
value of it, where the scalar acts by zero; a sheaf is separated. -/
theorem of_epi {S S' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (φ : S ⟶ S') [Epi φ] (h : SectionKills X a S) : SectionKills X a S' := by
  intro W g y
  obtain ⟨T, hT, hlift⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi φ (V := W.unop) y
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hT fun {V} k hk => ?_
  obtain ⟨t, ht⟩ := hlift k hk
  change S.val.obj (op V) at t
  change φ.val.app (op V) t = S'.val.map k.op y at ht
  have ht0 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map k.op
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g a) • t = 0 := by
    have := h (g ≫ k.op) t
    rwa [Functor.map_comp, RingCat.comp_apply] at this
  rw [PresheafOfModules.map_smul, ← ht]
  exact ((φ.val.app (op V)).hom.map_smul _ t).symm.trans (by rw [ht0, map_zero]; rfl)

/-- A zero object is killed by every section. -/
theorem of_isZero {S : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hS : IsZero S) : SectionKills X a S := by
  intro W g y
  have h0 : (𝟙 S : S ⟶ S).val.app W y = (0 : S ⟶ S).val.app W y := by
    rw [hS.eq_of_src (𝟙 S) 0]
  rw [show y = 0 from h0, smul_zero]

/-- Killing is invariant under isomorphism. -/
theorem of_iso {S S' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (e : S ≅ S') (h : SectionKills X a S) : SectionKills X a S' :=
  of_epi e.hom h

/-- **A section killing the right factor kills the tensor product sheaf.** The tensor product is
the sheafification of the objectwise tensor product, so a section is locally the image of an
element of a tensor product of modules of sections, which the scalar kills because it kills the
right-hand factor; a sheaf is separated. -/
theorem sheafTensor {N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : SectionKills X a N)
    (S : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SectionKills X a (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj S).obj N) := by
  intro W g s
  let P : PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj :=
    (((PresheafOfModules.tensorBifunctor (X.O).obj)).obj S.val).obj N.val
  let η := Stacks.SheafOfModules.TensorLocalProperties.sheafificationUnit
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) P
  have : PresheafOfModules.IsLocallySurjective X.J η :=
    inferInstanceAs (Presheaf.IsLocallySurjective X.J (CategoryTheory.toSheafify X.J P.presheaf))
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (J := X.J) _
    (Presheaf.imageSieve_mem X.J ((PresheafOfModules.toPresheaf _).map η) s) ?_
  intro V k hk
  obtain ⟨z, hz⟩ := hk
  change P.obj (op V) at z
  change η.app (op V) z = _ at hz
  have hz0 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map k.op
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g a) • z = 0 :=
    Stacks.SheafOfModules.smul_presheafTensorObj_eq_zero (R := X.O.obj) S.val N.val (op V) _
      (fun y => (h.map g) k.op y) z
  change η.app (op V) z =
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj S).obj N).val.map k.op s at hz
  rw [PresheafOfModules.map_smul, ← hz]
  exact ((η.app (op V)).hom.map_smul _ z).symm.trans (by rw [hz0, map_zero]; rfl)

end SectionKills

/-- **`fⁿ` kills `𝒪/ℐⁿ`** for a local section `f` of `ℐ`: every restriction of `fⁿ` is a
section of `ℐⁿ`, and the sections of `ℐⁿ` kill those of `𝒪/ℐⁿ`. -/
theorem sectionKills_pow_adicQuotientModule
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (n : ℕ)
    {U : X.Cᵒᵖ}
    {f : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U}
    (hf : f ∈ I.toSubmodule.obj U) :
    SectionKills X (f ^ n) (Stacks.Sites.adicQuotientModule (X := X) I n) := by
  intro W g y
  refine Stacks.Sites.smul_adicQuotientModule_eq_zero I n W _ ?_ y
  rw [map_pow]
  exact Stacks.Sites.mem_idealPow_of_mem_pow I n
    (Ideal.pow_mem_pow (Stacks.Sites.map_mem_sectionIdeal I g hf) n)

/-- A section over `U` killing `S` acts as zero on the restriction of `S` to the slice over
`U`. -/
theorem terminalSectionToEnd_app_overFunctor_eq_zero {U : X.C}
    {a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)}
    {S : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : SectionKills X a S) :
    (Stacks.SheafOfModules.terminalSectionToEnd
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) (Over.mk (𝟙 U))
        Over.mkIdTerminal a).app
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).obj S) =
      0 := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact (Stacks.SheafOfModules.terminalSectionToEnd_apply _ _ _ _ _ _ _).trans
    (h ((Over.mkIdTerminal (X := U)).from V.unop).left.op x)

end Sections

section Derived

/-- Multiplication by a scalar vanishes on an object as soon as it vanishes on an isomorphic
one. -/
theorem smul_id_eq_zero_of_iso {R : Type*} [Semiring R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] {A B : C} (e : A ≅ B) {r : R} (h : r • 𝟙 A = 0) :
    r • 𝟙 B = 0 := by
  have : r • 𝟙 B = e.inv ≫ (r • 𝟙 A) ≫ e.hom := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id]
  rw [this, h, zero_comp, comp_zero]

variable {U : X.C} {a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)}

/-- **A section killing every term of a complex acts as zero on the restriction of its class to
the slice.** Restriction is exact, so it computes the restricted class from the restricted
complex, on which the scalar acts as zero degreewise. -/
theorem smul_id_mapDerivedCategory_Q_eq_zero
    [(SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive]
    [PreservesFiniteLimits
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    [PreservesFiniteColimits
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    (T : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hT : ∀ k, SectionKills X a (T.X k)) :
    letI : Linear (CatCenter (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)))
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
      Linear.ofRingMorphism (RingHom.id _)
    Stacks.SheafOfModules.terminalSectionToEnd
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) (Over.mk (𝟙 U))
        Over.mkIdTerminal a •
      𝟙 ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.obj (DerivedCategory.Q.obj T)) = 0 := by
  let : Linear (CatCenter (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)))
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
    Linear.ofRingMorphism (RingHom.id _)
  let F := SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let θ := Stacks.SheafOfModules.terminalSectionToEnd
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) (Over.mk (𝟙 U)) Over.mkIdTerminal a
  refine smul_id_eq_zero_of_iso (F.mapDerivedCategoryFactors.app T).symm ?_
  have hc : θ • 𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T) = 0 := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    rw [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f, HomologicalComplex.zero_f]
    exact (Category.comp_id _).trans (terminalSectionToEnd_app_overFunctor_eq_zero (hT k))
  have hQ := Functor.Linear.map_smul (F := (DerivedCategory.Q :
    CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ
      ⥤ _)) (𝟙 ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T)) θ
  rw [CategoryTheory.Functor.map_id, hc, CategoryTheory.Functor.map_zero] at hQ
  exact hQ.symm

/-- The degree-`k` term of `Tot(P ⊗_𝒪 Q[0])` receives an epimorphism from `Pᵏ ⊗_𝒪 Q[0]⁰`:
the summand inclusion, the other summands being zero. -/
theorem epi_ιMapBifunctor_single
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (k : ℤ) :
    Epi (HomologicalComplex.ιMapBifunctor P ((CochainComplex.singleFunctor _ 0).obj Q)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) k 0 k
        (by simp)) := by
  refine ⟨fun f g hfg => ?_⟩
  refine HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ h => ?_
  by_cases hi₂ : i₂ = 0
  · subst hi₂
    obtain rfl : i₁ = k := by simpa using h
    exact hfg
  · exact (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (P.X i₁)).map_isZero
      (HomologicalComplex.isZero_single_obj_X _ 0 Q i₂ hi₂)).eq_of_src _ _

/-- **A section killing `Q` kills every term of `Tot(P ⊗_𝒪 Q[0])`.** -/
theorem sectionKills_mapBifunctor_single
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {W : X.Cᵒᵖ} {b : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj W}
    (hQ : SectionKills X b Q) (k : ℤ) :
    SectionKills X b ((HomologicalComplex.mapBifunctor P ((CochainComplex.singleFunctor _ 0).obj Q)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)).X k) := by
  have := epi_ιMapBifunctor_single X P Q k
  exact SectionKills.of_epi (HomologicalComplex.ιMapBifunctor P
    ((CochainComplex.singleFunctor _ 0).obj Q)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) k 0 k _)
    ((SectionKills.of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Q).symm hQ).sheafTensor _)

/-- **A section over `U` killing `Q` acts as zero on the restriction of `K ⊗^𝐋_𝒪 Q[0]` to the
slice over `U`**, for every `K ∈ D(𝒪)`. On a K-flat representative `P` of `K` the derived tensor
product is `Tot(P ⊗_𝒪 Q[0])`, all of whose terms the section kills. -/
theorem smul_id_overFunctor_derivedTensor_single_eq_zero
    [(SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive]
    [PreservesFiniteLimits
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    [PreservesFiniteColimits
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
    {Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hQ : SectionKills X a Q)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    letI : Linear (CatCenter (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)))
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
      Linear.ofRingMorphism (RingHom.id _)
    Stacks.SheafOfModules.terminalSectionToEnd
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) (Over.mk (𝟙 U))
        Over.mkIdTerminal a •
      𝟙 ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.obj
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
            ((DerivedCategory.singleFunctor _ 0).obj Q))) = 0 := by
  let : Linear (CatCenter (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)))
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
    Linear.ofRingMorphism (RingHom.id _)
  obtain ⟨P, hP, ⟨eP⟩⟩ := Stacks.SheafOfModules.Tensor.exists_kFlat_representative X K
  let T := Stacks.SheafOfModules.canonicalDerivedTensorProduct X
  let e : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
      ((DerivedCategory.singleFunctor _ 0).obj Q) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P
        ((CochainComplex.singleFunctor _ 0).obj Q)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
    (T.tensor.mapIso eP.symm).app _ ≪≫
      T.comparisonLeft P ((CochainComplex.singleFunctor _ 0).obj Q) hP
  refine smul_id_eq_zero_of_iso
    ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      U).mapDerivedCategory.mapIso e).symm ?_
  exact smul_id_mapDerivedCategory_Q_eq_zero X _ (sectionKills_mapBifunctor_single X P hQ)

end Derived

section Complete

/-- **Derived completeness from nilpotent action.** `K` is derived complete along `ℐ` as soon as
every local section `f ∈ ℐ(U)` has a power acting as zero on the restriction of `K` to the slice
over `U`. -/
private theorem isDerivedComplete_of_smul_id_pow_eq_zero
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (h : ∀ (V : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op V)),
      f ∈ I.toSubmodule.obj (op V) → ∃ n : ℕ,
      ∀ [(SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).Additive]
        [PreservesFiniteLimits
          (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)]
        [PreservesFiniteColimits
          (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V)],
      letI : Linear (CatCenter (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)))
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
        Linear.ofRingMorphism (RingHom.id _)
      Stacks.SheafOfModules.terminalSectionToEnd
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) (Over.mk (𝟙 V))
          Over.mkIdTerminal (f ^ n) •
        𝟙 ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          V).mapDerivedCategory.obj K) = 0) :
    IsDerivedComplete.{u, u, u, u} X I K := by
  intro V f hf
  let RV := ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over V
  let A := SheafOfModules.{u} RV
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let : ∀ W : (Over V)ᵒᵖ, IsMulCommutative (RV.obj.obj W) := fun W ↦ by
    show IsMulCommutative (X.O.obj.obj (op W.unop.left))
    infer_instance
  have hLim : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have hColim : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  have hProd : HasProductsOfShape ℕ (DerivedCategory A) :=
    hasProductsOfShape_nat_derivedCategory_over.{u, u, u} X V
  refine ⟨inferInstance, hLim, hColim, hProd, ?_⟩
  obtain ⟨n, hn⟩ := h V f hf
  refine isDerivedCompleteAt_of_isNilpotent ⟨n, ?_⟩
  rw [smul_id_pow, ← Stacks.SheafOfModules.terminalSectionToEnd_pow RV (Over.mk (𝟙 V))
    Over.mkIdTerminal f n]
  exact hn

/-- **[Stacks, Tag 0CQH], the derived completeness of the reductions.** For every sheaf of ideals
`ℐ ⊂ 𝒪`, every `K ∈ D(𝒪)` and every `n`, the derived reduction `K ⊗^𝐋_𝒪 𝒪/ℐⁿ` is derived
complete along `ℐ`, because it is annihilated by powers of local sections of `ℐ`: for
`f ∈ ℐ(U)`, multiplication by `fⁿ` is zero on its restriction to the slice over `U`, and a
scalar acting nilpotently is one at which every object is derived complete.

The source states this for `n ≥ 1` and a sheaf of ideals of finite type; neither restriction is
used (for `n = 0` the object is zero). -/
theorem isDerivedComplete_derivedTensor_adicQuotient
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (n : ℕ) :
    IsDerivedComplete.{u, u, u, u} X I
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
        (adicQuotientObj X I n)) := by
  refine isDerivedComplete_of_smul_id_pow_eq_zero X I _ fun V f hf => ⟨n, fun {_ _ _} => ?_⟩
  exact smul_id_overFunctor_derivedTensor_single_eq_zero X
    (sectionKills_pow_adicQuotientModule I n hf) K

/-- **A single complex is derived complete along `ℐ` as soon as every local section of `ℐ` has a
power killing its term.** Multiplication by that power is then zero on every restriction of the
complex to a slice. -/
theorem isDerivedComplete_single_of_sectionKills
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (Q : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hQ : ∀ (U : X.C) (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)),
      f ∈ I.toSubmodule.obj (op U) →
      ∃ n : ℕ, SectionKills X (f ^ n) Q) :
    IsDerivedComplete.{u, u, u, u} X I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj Q) := by
  refine isDerivedComplete_of_smul_id_pow_eq_zero X I _ fun V f hf => ?_
  obtain ⟨n, hn⟩ := hQ V f hf
  refine ⟨n, fun {_ _ _} => ?_⟩
  refine smul_id_mapDerivedCategory_Q_eq_zero X
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj Q) fun k => ?_
  by_cases hk : k = 0
  · subst hk
    exact SectionKills.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Q).symm hn
  · exact SectionKills.of_isZero (HomologicalComplex.isZero_single_obj_X _ 0 Q k hk)

/-- **`𝒪/ℐⁿ` is derived complete along `ℐ`**, for every sheaf of ideals `ℐ`: the `n`-th power of a
local section of `ℐ` kills it. -/
theorem isDerivedComplete_adicQuotientObj
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (n : ℕ) :
    IsDerivedComplete.{u, u, u, u} X I (adicQuotientObj X I n) :=
  isDerivedComplete_single_of_sectionKills X I _ fun _ _ hf =>
    ⟨n, sectionKills_pow_adicQuotientModule I n hf⟩

end Complete

end AlgebraicGeometry.RingedSite

end
