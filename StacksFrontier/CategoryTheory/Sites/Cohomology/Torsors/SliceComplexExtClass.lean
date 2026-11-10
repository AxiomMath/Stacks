module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SliceExtDeltaFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassSurjectivity

/-!
# The connecting map of a restricted short exact sequence on a glued section

Let `0 → S₁ → S₂ → S₃ → 0` be a short exact sequence of abelian sheaves on a site `C`, let
`𝒰 = {U_i → U}` be a covering family, and let `b` be a degree-zero Čech cochain of `S₂` whose
Čech differential comes from a Čech `1`-cocycle `z` of `S₁`. Then the image of `b` in `S₃` is
the restriction of a section `q` of `S₃` over `U`, by the sheaf condition in Čech form.

The torsor of `z` is classified, through Stacks 03AJ, by the connecting map of the sequence on
`C/U` obtained by restricting `S₁ → S₂` and taking its cokernel there, applied to the glued
section. This file shows that this class is the connecting map of the restriction of the whole
sequence `S` to `C/U`, applied to `q`: the cokernel comparison is a morphism of short exact
sequences which is the identity on the first two terms, and it carries the glued section to `q`.

## Main results

* `Stacks.Cohomology.Torsors.exists_cechAugmentationPre_eq_pushCochain`: the section `q`.
* `Stacks.Cohomology.Torsors.mk₀_comp_extClass_map_overPullback_eq`: the comparison of the two
  connecting maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

universe h t a w v u

namespace Stacks.Cohomology.Torsors

open Stacks.CechSite

attribute [local instance] HasDerivedCategory.standard

section Glue

variable {C : Type u} [Category.{v} C] {K : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U)
  [HasProducts.{w} AddCommGrpCat.{max a u v w}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- **The image of the cochain in the quotient sheaf is the restriction of a section over `U`.**
If the Čech differential of a degree-zero cochain `b` of `S₂` is the image of a Čech `1`-cocycle
`z` of `S₁`, then the image of `b` in `S₃` is the Čech augmentation of a section `q` of `S₃` over
`U`. -/
theorem exists_cechAugmentationPre_eq_pushCochain (hE : E.sieve₀ ∈ K U)
    (S : ShortComplex (Sheaf K AddCommGrpCat.{max a u v w}))
    (z : cocycles1 E S.X₁.obj) (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1)) :
    ∃ q : S.X₃.obj.obj (op U),
      productAddEquiv (cochainFactor E S.X₃.obj 0) (cechAugmentationPre.{a} E S.X₃.obj q) =
        pushCochain E S.g.hom 0 b := by
  obtain ⟨hl⟩ := nonempty_isLimit_kernelFork_cechAugmentationPre.{a} K E hE S.X₃
  have hex := ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk (cechAugmentationPre.{a} E S.X₃.obj)
      (((cechComplexFunctor E (A := AddCommGrpCat.{max a u v w})).obj S.X₃.obj).d 0 1)
      (cechAugmentationPre_comp_d.{a, w, v, u} E S.X₃.obj)) hl
  rw [ShortComplex.ab_exact_iff] at hex
  have h0 : cechDifferential E S.X₃.obj 0 (pushCochain E S.g.hom 0 b) = 0 := by
    rw [cechDifferential_pushCochain, hb, pushCochain_comp]
    funext k
    change (S.f ≫ S.g).hom.app _ _ = 0
    rw [S.zero]
    rfl
  let y : (cechComplex E S.X₃.obj).X 0 :=
    (productAddEquiv (cochainFactor E S.X₃.obj 0)).symm (pushCochain E S.g.hom 0 b)
  have hy : (cechComplex E S.X₃.obj).d 0 1 y = 0 := by
    apply (productAddEquiv (cochainFactor E S.X₃.obj 1)).injective
    rw [← cechDifferential_productAddEquiv, AddEquiv.apply_symm_apply, h0]
    exact (map_zero _).symm
  obtain ⟨q, hq⟩ := hex y hy
  exact ⟨q, (congrArg _ hq).trans (AddEquiv.apply_symm_apply _ _)⟩

end Glue

section CokernelComparison

variable {C : Type u} [Category.{v} C] {K : GrothendieckTopology C} (U : C)
  [HasSheafify K AddCommGrpCat.{t}] [HasSheafify (K.over U) AddCommGrpCat.{t}]
  [HasExt.{h} (Sheaf K AddCommGrpCat.{t})] (S : ShortComplex (Sheaf K AddCommGrpCat.{t}))

/-- The comparison from the cokernel of the restricted inclusion to the restricted quotient. -/
def sliceCokernelComparison :
    (sliceComplex U S).X₃ ⟶ S.X₃.over U :=
  cokernel.desc _ ((K.overPullback AddCommGrpCat.{t} U).map S.g)
    (by rw [← Functor.map_comp, S.zero, Functor.map_zero])

omit [HasSheafify K AddCommGrpCat.{t}] [HasExt.{h} (Sheaf K AddCommGrpCat.{t})] in
/-- The projection onto the cokernel of the restricted inclusion, followed by the cokernel
comparison, is the restriction of `S.g` to `C/U`. -/
@[reassoc (attr := simp)]
lemma π_sliceCokernelComparison :
    (sliceComplex U S).g ≫ sliceCokernelComparison U S =
      (K.overPullback AddCommGrpCat.{t} U).map S.g := by
  simp [sliceCokernelComparison]

/-- The cokernel comparison as a morphism of short complexes, the identity on the first two
terms. -/
def sliceComplexHom :
    sliceComplex U S ⟶ S.map (K.overPullback AddCommGrpCat.{t} U) where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := sliceCokernelComparison U S
  comm₁₂ := by simp
  comm₂₃ := (Category.id_comp _).trans (π_sliceCokernelComparison U S).symm

end CokernelComparison

section Comparison

variable {C : Type u} [Category.{v} C] {K : GrothendieckTopology C} {U : C}
  (E : PreZeroHypercover.{w} U)
  [HasProducts.{w} AddCommGrpCat.{max a u v w}]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify K AddCommGrpCat.{max a u v w}]
  [HasSheafify (K.over U) AddCommGrpCat.{max a u v w}]

omit [HasSheafify K AddCommGrpCat.{max a u v w}] in
/-- **The cokernel comparison carries the glued quotient section to the glued section of the
quotient sheaf.** Over `U`, the cokernel comparison sends the glued quotient section to every
section `q` of `S₃` whose Čech augmentation is the image of the cochain `b`. -/
theorem sliceCokernelComparison_app_glued (hE : E.sieve₀ ∈ K U)
    (S : ShortComplex (Sheaf K AddCommGrpCat.{max a u v w}))
    (z : cocycles1 E S.X₁.obj) (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1))
    (q : S.X₃.obj.obj (op U))
    (hq : productAddEquiv (cochainFactor E S.X₃.obj 0) (cechAugmentationPre.{a} E S.X₃.obj q) =
      pushCochain E S.g.hom 0 b) :
    (sliceCokernelComparison U S).hom.app (op (Over.mk (𝟙 U)))
      (Classical.choose (exists_glued_quotSection E S hE z b hb)) = q := by
  obtain ⟨hl⟩ := nonempty_isLimit_kernelFork_cechAugmentationPre.{a} K E hE S.X₃
  have hmono : Function.Injective (cechAugmentationPre.{a} E S.X₃.obj) :=
    (AddCommGrpCat.mono_iff_injective _).1 (Fork.IsLimit.mono hl)
  have hq' := Classical.choose_spec (exists_glued_quotSection E S hE z b hb)
  set q' := Classical.choose (exists_glued_quotSection E S hE z b hb)
  obtain ⟨r, hr⟩ : ∃ r : S.X₃.obj.obj (op U),
      (sliceCokernelComparison U S).hom.app (op (Over.mk (𝟙 U))) q' = r := ⟨_, rfl⟩
  rw [hr]
  have h1 : ∀ i : E.I₀, S.X₃.obj.map (E.f i).op r =
      S.g.hom.app (op (E.X i)) (cochainFam E S.X₂.obj b i) := by
    intro i
    have hn := NatTrans.naturality_apply (sliceCokernelComparison U S).hom
      (memberToTerminal E i).op q'
    rw [hq' i, hr] at hn
    exact hn.symm.trans <| congrArg (fun φ ↦ φ.hom.app (op (Over.mk (E.f i)))
      (cochainFam E S.X₂.obj b i)) (π_sliceCokernelComparison U S)
  apply hmono
  apply (productAddEquiv (cochainFactor E S.X₃.obj 0)).injective
  rw [hq]
  funext k
  change Pi.π (cochainFactor E S.X₃.obj 0) k (cechAugmentationPre.{a} E S.X₃.obj r) =
    S.g.hom.app _ (b k)
  rw [cechAugmentationPre_π_apply.{a, w, v, u}]
  have hfac : Over.mkIdTerminal.from (∏ᶜ fun j : Fin 1 ↦ Over.mk (E.f (k j))) =
      Pi.π (fun j : Fin 1 ↦ Over.mk (E.f (k j))) 0 ≫ memberToTerminal E (k 0) :=
    Over.mkIdTerminal.hom_ext _ _
  rw [hfac, Functor.map_comp, op_comp, Functor.map_comp_apply]
  change S.X₃.obj.map (Pi.π (fun j : Fin 1 ↦ Over.mk (E.f (k j))) 0).left.op
    (S.X₃.obj.map (E.f (k 0)).op r) = _
  rw [h1]
  conv_rhs => rw [← famCochain_cochainFam E S.X₂.obj b]
  exact (NatTrans.naturality_apply S.g.hom _ _).symm

omit [HasSheafify K AddCommGrpCat.{max a u v w}] in
/-- The glued quotient section, pushed along the cokernel comparison, is the section `q`, as a
morphism out of the constant presheaf of integers. -/
theorem quotGlobalSection_comp_sliceCokernelComparison (hE : E.sieve₀ ∈ K U)
    (S : ShortComplex (Sheaf K AddCommGrpCat.{max a u v w}))
    (z : cocycles1 E S.X₁.obj) (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1))
    (q : S.X₃.obj.obj (op U))
    (hq : productAddEquiv (cochainFactor E S.X₃.obj 0) (cechAugmentationPre.{a} E S.X₃.obj q) =
      pushCochain E S.g.hom 0 b) :
    quotGlobalSection E S hE z b hb ≫ (sliceCokernelComparison U S).hom =
      terminalSectionFamily (S.X₃.over U).obj q := by
  apply NatTrans.ext
  funext W
  apply liftedInt_hom_ext
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply]
  refine Eq.trans ?_ (terminalSectionFamily_app (S.X₃.over U).obj q W).symm
  refine (congrArg ((sliceCokernelComparison U S).hom.app W)
    (terminalSectionFamily_app _ _ W)).trans ?_
  refine (NatTrans.naturality_apply (sliceCokernelComparison U S).hom _ _).trans ?_
  exact congrArg _ (sliceCokernelComparison_app_glued E hE S z b hb q hq)

variable [K.WEqualsLocallyBijective AddCommGrpCat.{max a u v w}]
  [HasExt.{max a u v w} (Sheaf (K.over U) AddCommGrpCat.{max a u v w})]

/-- **The class of the torsor of a Čech cocycle is the connecting map of the restricted sequence
applied to the glued section.** The connecting map of the sequence on `C/U` built from the
cokernel of the restricted inclusion, applied to the glued quotient section, equals the
connecting map of the restriction of `S` itself applied to a section `q` of `S₃` over `U` whose
restrictions are the images of the cochain. -/
theorem mk₀_comp_extClass_map_overPullback_eq (hE : E.sieve₀ ∈ K U)
    (S : ShortComplex (Sheaf K AddCommGrpCat.{max a u v w})) (hS : S.ShortExact)
    (z : cocycles1 E S.X₁.obj) (b : cechCochain E S.X₂.obj 0)
    (hb : cechDifferential E S.X₂.obj 0 b =
      pushCochain E S.f.hom 1 (z : cechCochain E S.X₁.obj 1))
    (q : S.X₃.obj.obj (op U))
    (hq : productAddEquiv (cochainFactor E S.X₃.obj 0) (cechAugmentationPre.{a} E S.X₃.obj q) =
      pushCochain E S.g.hom 0 b) :
    (Ext.mk₀ (((sheafificationAdjunction (K.over U) AddCommGrpCat.{max a u v w}).homEquiv
          (sliceUnitPresheaf.{max a u v w} U) (S.X₃.over U)).symm
            (terminalSectionFamily (S.X₃.over U).obj q))).comp
        (hS.map_of_exact (K.overPullback AddCommGrpCat.{max a u v w} U)).extClass (zero_add 1) =
      (Ext.mk₀ (((sheafificationAdjunction (K.over U) AddCommGrpCat.{max a u v w}).homEquiv
          (sliceUnitPresheaf.{max a u v w} U) (sliceComplex U S).X₃).symm
          (quotGlobalSection E S hE z b hb))).comp
        (sliceComplex_shortExact U S hS).extClass (zero_add 1) := by
  have hadj : ((sheafificationAdjunction (K.over U) AddCommGrpCat.{max a u v w}).homEquiv
        (sliceUnitPresheaf.{max a u v w} U) (S.X₃.over U)).symm
        (quotGlobalSection E S hE z b hb ≫ (sliceCokernelComparison U S).hom) =
      ((sheafificationAdjunction (K.over U) AddCommGrpCat.{max a u v w}).homEquiv
        (sliceUnitPresheaf.{max a u v w} U) (sliceComplex U S).X₃).symm
        (quotGlobalSection E S hE z b hb) ≫ sliceCokernelComparison U S :=
    Adjunction.homEquiv_naturality_right_symm _ _ _
  have hnat' : (Ext.mk₀ (sliceCokernelComparison U S)).comp
      (hS.map_of_exact (K.overPullback AddCommGrpCat.{max a u v w} U)).extClass (zero_add 1) =
      (sliceComplex_shortExact U S hS).extClass :=
    ((sliceComplex_shortExact U S hS).extClass_naturality
      (hS.map_of_exact (K.overPullback AddCommGrpCat.{max a u v w} U))
      (sliceComplexHom U S)).symm.trans (Ext.comp_mk₀_id _)
  rw [← quotGlobalSection_comp_sliceCokernelComparison E hE S z b hb q hq, hadj,
    ← Ext.mk₀_comp_mk₀_assoc, hnat']

end Comparison

end Stacks.Cohomology.Torsors
