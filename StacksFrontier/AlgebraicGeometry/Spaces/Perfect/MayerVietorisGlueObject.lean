module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.EtaleDerivedPushforwardAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedOnComplementClauses
public import StacksFrontier.CategoryTheory.Adjunction.AdjunctionUnit

/-!
# The glued object of an elementary distinguished square

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` be its intersection and write `(-)|_Y` for restriction of modules
along the étale morphism `j_Y : Y ⟶ X`.  The first assertion of Stacks 08HB says that an object
`A` of `D(𝒪_U)`, an object `B` of `D(𝒪_V)` and an isomorphism `c : A|_P ⟶ B|_P` are glued by an
object `F` of `D(𝒪_X)` and isomorphisms `f : F|_U ⟶ A`, `g : F|_V ⟶ B` with
`c = g|_P ∘ f^{-1}|_P`.  This file proves it, by the source's argument: `F` is the fibre of

`Rj_{U,*}A ⊕ Rj_{V,*}B ⟶ Rj_{P,*}(B|_P)`.

## Main results

* `CategoryTheory.isIso_fst_of_distinguished_triangle` and
  `…isIso_map_fst_of_distinguished_triangle`: in a distinguished triangle
  `F ⟶ A ⊞ B ⟶ W ⟶ F[1]` whose second map is invertible on the `B`-summand, the `A`-coordinate
  of the first map is invertible, and a triangulated functor inverting the former inverts the
  latter.
* `CategoryTheory.isIso_of_isIso_map_of_bijective_comp_on_kernel`: a triangulated functor is
  conservative on the morphisms it inverts, given bijectivity of composition on the objects it
  kills.
* `CategoryTheory.isZero_restrict_rightAdjoint_of_isZero_restrict`: given adjunctions
  `sh_U ⊣ r_U`, `r_V ⊣ R_V`, `sh_P ⊣ r_{VP}` and an identification
  `r_{UP} ⋙ sh_P ≅ sh_U ⋙ r_V`, the object `r_U(R_V Z)` vanishes whenever `r_{VP} Z` does.
* `CategoryTheory.exists_gluing_triangle`: the fibre of the difference of the two canonical
  maps into `R_P(Q_V B)`, with the two transposes it carries and their compatibility with `c`.
* `CategoryTheory.exists_glue_of_restrictionData`: the whole triangulated argument for the
  existence of the glued object, in an arbitrary pretriangulated category with the four
  adjunctions, the extension by zero on `V` and the two identifications of iterated
  restrictions.
* `AlgebraicGeometry.Space.isIso_etaleModuleLowerShriekAdjunction_unit` and
  `…isIso_derivedEtaleModuleLowerShriekAdjunction_unit`: along an open immersion the unit
  `M ⟶ (j_!M)|_U` of extension by zero against restriction is an isomorphism, on modules and
  on unbounded derived categories.
* `AlgebraicGeometry.Space.isIso_counit_mapDerivedCategory_of_isOpenImmersion`: along an open
  immersion the counit `(R E)|_U ⟶ E` of any right adjoint `R` of derived restriction is an
  isomorphism.
* `AlgebraicGeometry.Space.isIso_unit_mapDerivedCategory_lowerShriek_of_isZero_edsRestrictSnd`:
  the unit `Z ⟶ (j_{V!}Z)|_V` is an isomorphism as soon as `Z|_P = 0`; this is where the
  defining condition of the square enters, through clause (1)(b) of Stacks 08GG.
* `AlgebraicGeometry.Space.exists_glued_object`: **the first assertion of Stacks 08HB**.

## Implementation notes

The compatibility `c = g|_P ∘ f^{-1}|_P` is written with the two identifications
`AlgebraicGeometry.Space.edsDerivedRestrictCompOpen` and `…edsDerivedRestrictCompEtale` of the
two iterated restrictions with the restriction to `P`, which the source writes silently; it is
the spelling of the hypothesis `hc` of the induced-morphism statement, so the two assertions
compose in `StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisGlueingTag.lean`.

The derived direct images are not data of the statement.  Each is a right adjoint of derived
restriction, which exists by
`AlgebraicGeometry.Space.nonempty_etaleModulePullback_mapDerivedCategory_adjunction`; its
additivity, its shift-commutation and its triangulatedness are those of a right adjoint of a
triangulated functor.  Extension by zero is `AlgebraicGeometry.Space.etaleModuleLowerShriek`.

## References

* [Stacks Project, Tag 08HB](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08HA](https://stacks.math.columbia.edu/tag/08HA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory

section Construct

/-- A morphism into the value of a right adjoint vanishes as soon as the left adjoint kills
its source: its transpose is a morphism out of a zero object. -/
theorem hom_eq_zero_of_isZero_leftAdjoint {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] {Z : C} (hZ : IsZero (L.obj Z)) {A : D} (f : Z ⟶ R.obj A) : f = 0 := by
  apply (adj.homEquiv Z A).symm.injective
  rw [adj.homAddEquiv_symm_zero]
  exact hZ.eq_of_src _ _

/-- A morphism out of the value of a left adjoint vanishes as soon as the right adjoint kills
its target: its transpose is a morphism into a zero object. -/
theorem hom_eq_zero_of_isZero_rightAdjoint {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [HasZeroMorphisms C] [HasZeroMorphisms D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : D} (hA : IsZero (R.obj A)) {Z : C} (f : L.obj Z ⟶ A) : f = 0 :=
  (adj.homEquiv Z A).injective (hA.eq_of_tgt _ _)

/-- A morphism into the value of an additive right adjoint vanishes if its transpose does. -/
private theorem eq_zero_of_homEquiv_symm_eq_zero {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [Preadditive C] [Preadditive D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [R.Additive] {X : C} {Y : D} (f : X ⟶ R.obj Y) (h : (adj.homEquiv X Y).symm f = 0) :
    f = 0 := by
  rw [← (adj.homEquiv X Y).apply_symm_apply f, h, Adjunction.homEquiv_unit, Functor.map_zero,
    comp_zero]

/-- **The restriction of a right adjoint vanishes where the restriction of its argument does.**
Let `adjU : sh_U ⊣ r_U` and `adjP : sh_P ⊣ r_{VP}` be adjunctions of extension-by-zero type,
let `adjV : r_V ⊣ R_V` exhibit `R_V` as a right adjoint of `r_V`, and let
`e : r_{UP} ⋙ sh_P ≅ sh_U ⋙ r_V` be the base-change identification of the two composites from
`DU` to `DV`.  Then `r_U(R_V Z)` vanishes for every object `Z` with `r_{VP} Z = 0`.

Indeed a morphism `r_U(R_V Z) ⟶ r_U(R_V Z)` transposes across `adjU`, then across `adjV`, then
across `e` and `adjP`, into a morphism with target `r_{VP} Z = 0`; so the identity of
`r_U(R_V Z)` vanishes. -/
theorem isZero_restrict_rightAdjoint_of_isZero_restrict {DX : Type u₁} [Category.{v₁} DX]
    [Preadditive DX] {DU : Type u₂} [Category.{v₂} DU] [Preadditive DU] {DV : Type u₃}
    [Category.{v₃} DV] [Preadditive DV] {DP : Type u₄} [Category.{v₄} DP] [Preadditive DP]
    {rU : DX ⥤ DU} {shU : DU ⥤ DX} (adjU : shU ⊣ rU)
    {rV : DX ⥤ DV} {RV : DV ⥤ DX} (adjV : rV ⊣ RV)
    {rVP : DV ⥤ DP} {shP : DP ⥤ DV} (adjP : shP ⊣ rVP)
    {rUP : DU ⥤ DP} (e : rUP ⋙ shP ≅ shU ⋙ rV) [rU.Additive] [RV.Additive]
    {Z : DV} (hZ : IsZero (rVP.obj Z)) : IsZero (rU.obj (RV.obj Z)) := by
  rw [IsZero.iff_id_eq_zero]
  have hV : ∀ β : rV.obj (shU.obj (rU.obj (RV.obj Z))) ⟶ Z, β = 0 := by
    intro β
    have h := hom_eq_zero_of_isZero_rightAdjoint adjP hZ (e.hom.app (rU.obj (RV.obj Z)) ≫ β)
    calc β = e.inv.app (rU.obj (RV.obj Z)) ≫ e.hom.app (rU.obj (RV.obj Z)) ≫ β := by simp
      _ = 0 := by rw [h, comp_zero]
  have hX : ∀ α : shU.obj (rU.obj (RV.obj Z)) ⟶ RV.obj Z, α = 0 := fun α =>
    eq_zero_of_homEquiv_symm_eq_zero adjV α (hV _)
  exact eq_zero_of_homEquiv_symm_eq_zero adjU (𝟙 _) (hX _)

/-- **A distinguished triangle whose second map is a split epi onto a biproduct summand.**  If
`F ⟶ A ⊞ B ⟶ W ⟶ F[1]` is distinguished and the `B`-component `b : B ⟶ W` of its second map is
invertible, then the `A`-component `F ⟶ A` of its first map is invertible: the second map is a
split epi, so the first is a mono, and the `B`-coordinate of the first map is determined by its
`A`-coordinate. -/
theorem isIso_fst_of_distinguished_triangle {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {F A B W : C} (f : F ⟶ A ⊞ B) (a : A ⟶ W) (b : B ⟶ W) (δ : W ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f (biprod.desc a b) δ ∈ distTriang C) [IsIso b] :
    IsIso (f ≫ biprod.fst) := by
  have hb : Epi (biprod.desc a b) := by
    have : IsSplitEpi (biprod.desc a b) :=
      IsSplitEpi.mk' ⟨inv b ≫ biprod.inr, by simp⟩
    infer_instance
  have hf : Mono f := Triangle.mono₁ _ hT (Triangle.mor₃_eq_zero_of_epi₂ _ hT hb)
  have hz : f ≫ biprod.desc a b = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hf₂ : f ≫ biprod.snd = -(f ≫ biprod.fst ≫ a ≫ inv b) := by
    apply (cancel_mono b).1
    have h : f ≫ biprod.fst ≫ a + f ≫ biprod.snd ≫ b = 0 := by
      simpa only [biprod.desc_eq, Preadditive.comp_add, Category.assoc] using hz
    simpa using eq_neg_of_add_eq_zero_right h
  apply isIso_of_yoneda_map_bijective
  intro Z
  constructor
  · intro x y hxy
    apply (cancel_mono f).1
    apply biprod.hom_ext
    · simpa only [Category.assoc] using hxy
    · simp only [Category.assoc, hf₂, Preadditive.comp_neg]
      simpa only [← Category.assoc] using congrArg (fun q => -(q ≫ a ≫ inv b)) hxy
  · intro x
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ _ hT
      (biprod.lift x (-(x ≫ a ≫ inv b))) (by simp)
    refine ⟨y, ?_⟩
    simpa only [Triangle.mk_mor₁, Category.assoc, biprod.lift_fst] using
      (congrArg (fun q => q ≫ biprod.fst) hy).symm

/-- The image of `CategoryTheory.isIso_fst_of_distinguished_triangle` under a triangulated
functor: if `L` inverts the `B`-component of the second map of a distinguished triangle
`F ⟶ A ⊞ B ⟶ W ⟶ F[1]`, then `L` inverts the `A`-component of its first map. -/
theorem isIso_map_fst_of_distinguished_triangle {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (L : C ⥤ D) [L.Additive] [L.CommShift ℤ] [L.IsTriangulated]
    {F A B W : C} (t : F ⟶ A ⊞ B) (a : A ⟶ W) (b : B ⟶ W) (δ : W ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk t (biprod.desc a b) δ ∈ distTriang C) [IsIso (L.map b)] :
    IsIso (L.map (t ≫ biprod.fst)) := by
  have := preservesBinaryBiproducts_of_preservesBinaryProducts L
  have hmap : Triangle.mk (L.map t) (L.map (biprod.desc a b))
      (L.map δ ≫ (L.commShiftIso (1 : ℤ)).hom.app F) ∈ distTriang D :=
    L.map_distinguished _ hT
  have hT' : Triangle.mk (L.map t ≫ (L.mapBiprod A B).hom)
      (biprod.desc (L.map a) (L.map b))
      (L.map δ ≫ (L.commShiftIso (1 : ℤ)).hom.app F) ∈ distTriang D := by
    refine isomorphic_distinguished _ hmap _
      (Triangle.isoMk _ _ (Iso.refl _) (L.mapBiprod A B).symm (Iso.refl _) ?_ ?_ ?_)
    · simp only [Triangle.mk_mor₁, Triangle.mk_obj₁, Iso.symm_hom, Iso.refl_hom,
        Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Triangle.mk_mor₂, Triangle.mk_obj₃, Iso.symm_hom, Iso.refl_hom,
        Category.comp_id, biprod.mapBiprod_inv_map_desc]
    · simp
  have h := isIso_fst_of_distinguished_triangle _ _ _ _ hT'
  simpa only [Functor.map_comp, Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst] using h

/-- **Conservativity of a triangulated functor on the subcategory it does not kill.**  Let `P`
be a triangulated functor and `g : X ⟶ Y` a morphism with `P g` invertible.  If composition
with `g` is bijective on morphisms out of every object that `P` kills, then `g` itself is
invertible: the cone of `g` is killed by `P`, hence the connecting map out of it vanishes, so
`g` is a split mono whose cone has a vanishing identity. -/
theorem isIso_of_isIso_map_of_bijective_comp_on_kernel {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (P : C ⥤ D) [P.Additive] [P.CommShift ℤ] [P.IsTriangulated]
    {X Y : C} (g : X ⟶ Y) [IsIso (P.map g)]
    (hg : ∀ Z, IsZero (P.obj Z) → Function.Bijective (fun a : Z ⟶ X => a ≫ g)) : IsIso g := by
  obtain ⟨K, b, δ, hT⟩ := distinguished_cocone_triangle g
  let T := Triangle.mk g b δ
  have hK : IsZero (P.obj K) :=
    (P.mapTriangle.obj T).isZero₃_of_isIso₁ (P.map_distinguished T hT)
      (by change IsIso (P.map g); infer_instance)
  have hK' : IsZero (P.obj (K⟦(-1 : ℤ)⟧)) :=
    ((shiftFunctor D (-1)).map_isZero hK).of_iso ((P.commShiftIso (-1)).app K)
  have hα : T.invRotate.mor₁ = 0 := by
    apply (hg _ hK').1
    exact (comp_distTriang_mor_zero₁₂ _ (inv_rot_of_distTriang T hT)).trans zero_comp.symm
  have hm : Mono g := T.invRotate.mono₂ (inv_rot_of_distTriang T hT) hα
  have hδ : δ = 0 := T.mor₃_eq_zero_of_mono₁ hT hm
  obtain ⟨a, ha⟩ := T.coyoneda_exact₃ hT (𝟙 K) (by change 𝟙 K ≫ δ = 0; simp [hδ])
  obtain ⟨a', ha'⟩ := (hg K hK).2 a
  have hid : 𝟙 K = 0 := by
    rw [ha, ← ha', Category.assoc]
    change a' ≫ (g ≫ b) = 0
    have hgb : g ≫ b = 0 := comp_distTriang_mor_zero₁₂ _ hT
    rw [hgb, comp_zero]
  exact (T.isZero₃_iff_isIso₁ hT).mp ((IsZero.iff_id_eq_zero K).mpr hid)

/-- **Composition with the second coordinate of the first map of a distinguished triangle.**
Let `F ⟶ A ⊞ B ⟶ W ⟶ F[1]` be distinguished with first map `(u, v)` and let `Z` be an object
admitting no nonzero morphism to `A`, to `W` or to `W[-1]`.  Then composition with `v` is a
bijection from morphisms `Z ⟶ F` to morphisms `Z ⟶ B`. -/
theorem bijective_comp_snd_of_distinguished_triangle {C : Type u₁} [Category.{v₁} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {F A B W Z : C} (u : F ⟶ A) (v : F ⟶ B) (d : A ⊞ B ⟶ W) (δ : W ⟶ F⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift u v) d δ ∈ distTriang C)
    (hA : ∀ a : Z ⟶ A, a = 0) (hW : ∀ a : Z ⟶ W, a = 0)
    (hW' : ∀ a : Z ⟶ W⟦(-1 : ℤ)⟧, a = 0) :
    Function.Bijective (fun a : Z ⟶ F => a ≫ v) := by
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    have ht : (a - b) ≫ biprod.lift u v = 0 := by
      apply biprod.hom_ext
      · simpa only [Category.assoc, biprod.lift_fst, zero_comp] using hA ((a - b) ≫ u)
      · simp only [Category.assoc, biprod.lift_snd, zero_comp, Preadditive.sub_comp, hab, sub_self]
    obtain ⟨c, hc⟩ := (Triangle.mk (biprod.lift u v) d δ).invRotate.coyoneda_exact₂
      (inv_rot_of_distTriang _ hT) (a - b) ht
    rw [hc, hW' c]
    exact zero_comp
  · intro b
    obtain ⟨a, ha⟩ := Triangle.coyoneda_exact₂ _ hT (biprod.lift 0 b)
      (hW (biprod.lift 0 b ≫ d))
    refine ⟨a, ?_⟩
    simpa only [Triangle.mk_mor₁, Category.assoc, biprod.lift_snd] using
      (congrArg (fun t => t ≫ biprod.snd) ha).symm

/-- **Transport of a bijection along two adjunctions.**  Let `a : L ⊣ R` and `b : E ⊣ L`, and
let `Z` be an object at which the unit of `b` is invertible.  If composition with
`v : F ⟶ R B` is bijective on morphisms out of `E Z`, then composition with the transpose of
`v` is bijective on morphisms out of `Z`. -/
theorem bijective_comp_of_adjunctions {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {L : C ⥤ D} {R E : D ⥤ C} (a : L ⊣ R) (b : E ⊣ L)
    (Z : D) [IsIso (b.unit.app Z)] {F : C} {B : D} (v : F ⟶ R.obj B)
    (hv : Function.Bijective (fun x : E.obj Z ⟶ F => x ≫ v)) :
    Function.Bijective (fun x : Z ⟶ L.obj F => x ≫ (a.homEquiv F B).symm v) := by
  let eL := b.homEquiv Z F
  let eR : (E.obj Z ⟶ R.obj B) ≃ (Z ⟶ B) :=
    (a.homEquiv (E.obj Z) B).symm.trans
      { toFun := fun x => b.unit.app Z ≫ x
        invFun := fun x => inv (b.unit.app Z) ≫ x
        left_inv := by intro x; simp
        right_inv := by intro x; simp }
  have ht (x : E.obj Z ⟶ F) : eR (x ≫ v) = eL x ≫ (a.homEquiv F B).symm v := by
    dsimp only [eR, Equiv.trans_apply, Equiv.coe_fn_mk, eL]
    rw [a.homEquiv_naturality_left_symm]
    simp only [Adjunction.homEquiv_apply, Category.assoc]
  simpa only [Function.comp_def, ht, Equiv.apply_symm_apply] using
    eR.bijective.comp (hv.comp eL.symm.bijective)

/-- The transpose of `x ≫ α` where `α` is itself the transpose of a composite built from the
counit of `L ⊣ R` read through `e : L ⋙ Q ≅ H`: it is the transpose of `x` pushed through `Q`
and conjugated by `e`. -/
theorem adjoint_restriction_map {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {L : C ⥤ D} {R : D ⥤ C} {H : C ⥤ E} {T : E ⥤ C}
    (Q : D ⥤ E) (adjL : L ⊣ R) (adjH : H ⊣ T) (e : L ⋙ Q ≅ H)
    {F : C} {A : D} {Z : E} (x : F ⟶ R.obj A) (c : Q.obj A ⟶ Z) :
    (adjH.homEquiv F Z).symm
        (x ≫ adjH.homEquiv (R.obj A) Z
          (e.inv.app (R.obj A) ≫ Q.map (adjL.counit.app A) ≫ c)) =
      e.inv.app F ≫ Q.map ((adjL.homEquiv F A).symm x) ≫ c := by
  rw [adjH.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [e.inv.naturality_assoc]
  rfl

/-- **The glueing triangle.**  Let `r_U ⊣ R_U`, `r_V ⊣ R_V` and `r_P ⊣ R_P` be adjunctions out
of a pretriangulated category `C`, let `Q_U` and `Q_V` be functors with
`e_U : r_U ⋙ Q_U ≅ r_P` and `e_V : r_V ⋙ Q_V ≅ r_P`, and let `c : Q_U A ≅ Q_V B` be an
isomorphism.  The fibre `F` of the difference of the two canonical maps
`R_U A ⟶ R_P (Q_V B)` and `R_V B ⟶ R_P (Q_V B)` comes with maps `u : F ⟶ R_U A` and
`v : F ⟶ R_V B` whose transposes `r_U F ⟶ A` and `r_V F ⟶ B` induce `c` on the overlap.

This is the object the source of Stacks 08HB builds as the fibre of
`Rj_{U,*}A ⊕ Rj_{V,*}B ⟶ Rj_{U ×_X V,*}(B|_{U ×_X V})`. -/
theorem exists_gluing_triangle {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {W : Type u₄} [Category.{v₄} W]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {LU : C ⥤ D} {RU : D ⥤ C} {LV : C ⥤ E} {RV : E ⥤ C} {H : C ⥤ W} {R : W ⥤ C}
    (PU : D ⥤ W) (PV : E ⥤ W) (adjU : LU ⊣ RU) (adjV : LV ⊣ RV) (adjH : H ⊣ R)
    (eU : LU ⋙ PU ≅ H) (eV : LV ⋙ PV ≅ H)
    (A : D) (B : E) (c : PU.obj A ≅ PV.obj B) :
    let aU := adjH.homEquiv (RU.obj A) (PV.obj B)
      (eU.inv.app (RU.obj A) ≫ PU.map (adjU.counit.app A) ≫ c.hom)
    let aV := adjH.homEquiv (RV.obj B) (PV.obj B)
      (eV.inv.app (RV.obj B) ≫ PV.map (adjV.counit.app B) ≫ 𝟙 _)
    ∃ (F : C) (u : F ⟶ RU.obj A) (v : F ⟶ RV.obj B) (δ : R.obj (PV.obj B) ⟶ F⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift u v) (biprod.desc aU (-aV)) δ ∈ distTriang C ∧
        PU.map ((adjU.homEquiv F A).symm u) ≫ c.hom =
          eU.hom.app F ≫ eV.inv.app F ≫ PV.map ((adjV.homEquiv F B).symm v) := by
  dsimp only
  let aU := adjH.homEquiv (RU.obj A) (PV.obj B)
    (eU.inv.app (RU.obj A) ≫ PU.map (adjU.counit.app A) ≫ c.hom)
  let aV := adjH.homEquiv (RV.obj B) (PV.obj B)
    (eV.inv.app (RV.obj B) ≫ PV.map (adjV.counit.app B) ≫ 𝟙 _)
  obtain ⟨F, t, δ, hT⟩ := distinguished_cocone_triangle₁ (biprod.desc aU (-aV))
  have ht : biprod.lift (t ≫ biprod.fst) (t ≫ biprod.snd) = t := by
    apply biprod.hom_ext <;> simp
  refine ⟨F, t ≫ biprod.fst, t ≫ biprod.snd, δ, ?_, ?_⟩
  · simpa only [ht] using hT
  · have hz : t ≫ biprod.desc aU (-aV) = 0 := comp_distTriang_mor_zero₁₂ _ hT
    have he : (t ≫ biprod.fst) ≫ aU = (t ≫ biprod.snd) ≫ aV := by
      rw [← ht, biprod.lift_desc, Preadditive.comp_neg, ← sub_eq_add_neg] at hz
      exact sub_eq_zero.mp hz
    have h := congrArg (adjH.homEquiv F (PV.obj B)).symm he
    rw [adjoint_restriction_map, adjoint_restriction_map] at h
    have h' := congrArg (fun q => eU.hom.app F ≫ q) h
    dsimp only [Functor.id_obj] at h'
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Category.comp_id] using h'

/-- **The second canonical map of the glueing triangle factors through the unit.**  The
transpose of the composite of the counit of `a : L ⊣ R` with `e : L ⋙ Q ≅ H` is the image
under `R` of the unit of `b : Q ⊣ S`, followed by the comparison of the two right adjoints of
`L ⋙ Q`.  This is what exhibits the `V`-component of the glueing triangle as a unit map. -/
theorem adjoint_factor {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {W : Type u₄} [Category.{v₄} W] {L : C ⥤ D} {R : D ⥤ C} {Q : D ⥤ W} {S : W ⥤ D}
    {H : C ⥤ W} {T : W ⥤ C} (a : L ⊣ R) (b : Q ⊣ S) (d : H ⊣ T) (e : L ⋙ Q ≅ H) (B : D) :
    d.homEquiv (R.obj B) (Q.obj B) (e.inv.app (R.obj B) ≫ Q.map (a.counit.app B)) =
      R.map (b.unit.app B) ≫
        (Adjunction.rightAdjointUniq ((a.comp b).ofNatIsoLeft e) d).hom.app (Q.obj B) := by
  apply (d.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, d.homEquiv_naturality_left_symm]
  have key : (d.homEquiv (R.obj ((Q ⋙ S).obj B)) (Q.obj B)).symm
      ((Adjunction.rightAdjointUniq ((a.comp b).ofNatIsoLeft e) d).hom.app (Q.obj B)) =
      ((a.comp b).ofNatIsoLeft e).counit.app (Q.obj B) :=
    Adjunction.homEquiv_symm_rightAdjointUniq_hom_app _ _ _
  rw [key]
  have hcounit : ((a.comp b).ofNatIsoLeft e).counit.app (Q.obj B) =
      e.inv.app (R.obj (S.obj (Q.obj B))) ≫
        Q.map (a.counit.app (S.obj (Q.obj B))) ≫ b.counit.app (Q.obj B) := by
    simp only [Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
      Functor.map_id, Category.id_comp]
    simp
  rw [hcounit]
  have hnatE : H.map (R.map (b.unit.app B)) ≫ e.inv.app (R.obj (S.obj (Q.obj B))) =
      e.inv.app (R.obj B) ≫ Q.map (L.map (R.map (b.unit.app B))) :=
    e.inv.naturality (R.map (b.unit.app B))
  have hnatC : L.map (R.map (b.unit.app B)) ≫ a.counit.app (S.obj (Q.obj B)) =
      a.counit.app B ≫ b.unit.app B := a.counit.naturality (b.unit.app B)
  have htri : Q.map (b.unit.app B) ≫ b.counit.app (Q.obj B) = 𝟙 (Q.obj B) :=
    b.left_triangle_components B
  rw [reassoc_of% hnatE, ← Q.map_comp_assoc, hnatC, Q.map_comp, Category.assoc, htri]
  simp

/-- **A triangulated functor inverts a unit map whose cone it kills.**  Let `adj : L ⊣ R` with
`L` triangulated and invertible counit, and let `F` be a triangulated functor killing every
object that `L` kills.  Then `F` inverts the unit of `adj` at every object. -/
theorem isIso_map_unit_of_kernel_le {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [Preadditive E] [HasZeroObject E] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Additive] [L.CommShift ℤ] [L.IsTriangulated] [IsIso adj.counit]
    (F : C ⥤ E) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ Z, IsZero (L.obj Z) → IsZero (F.obj Z)) (A : C) :
    IsIso (F.map (adj.unit.app A)) := by
  have : IsIso (L.map (adj.unit.app A)) := by
    have : IsIso (L.map (adj.unit.app A) ≫ adj.counit.app (L.obj A)) := by
      rw [adj.left_triangle_components A]
      exact (Iso.refl (L.obj A)).isIso_hom
    exact IsIso.of_isIso_comp_right _ (adj.counit.app (L.obj A))
  obtain ⟨Z, b, δ, hT⟩ := distinguished_cocone_triangle (adj.unit.app A)
  have hL : IsZero (L.obj Z) :=
    (L.mapTriangle.obj _).isZero₃_of_isIso₁ (L.map_distinguished _ hT) (by
      change IsIso (L.map (adj.unit.app A))
      assumption)
  exact ((F.mapTriangle.obj _).isZero₃_iff_isIso₁ (F.map_distinguished _ hT)).mp (hF Z hL)

end Construct

section Glueing

variable {DX : Type u₁} [Category.{v₁} DX] [Preadditive DX] [HasZeroObject DX]
  [HasBinaryBiproducts DX] [HasShift DX ℤ] [∀ n : ℤ, (shiftFunctor DX n).Additive]
  [Pretriangulated DX]
  {DU : Type u₂} [Category.{v₂} DU] [Preadditive DU] [HasZeroObject DU] [HasShift DU ℤ]
  [∀ n : ℤ, (shiftFunctor DU n).Additive] [Pretriangulated DU]
  {DV : Type u₃} [Category.{v₃} DV] [Preadditive DV] [HasZeroObject DV] [HasShift DV ℤ]
  [∀ n : ℤ, (shiftFunctor DV n).Additive] [Pretriangulated DV]
  {DP : Type u₄} [Category.{v₄} DP] [Preadditive DP] [HasZeroObject DP] [HasShift DP ℤ]
  [∀ n : ℤ, (shiftFunctor DP n).Additive] [Pretriangulated DP]

/-- **Glueing an object out of a restriction datum along a Mayer–Vietoris situation.**  Let
`DX`, `DU`, `DV`, `DP` be pretriangulated categories, let

* `adjU : r_U ⊣ R_U`, `adjV : r_V ⊣ R_V`, `adjP : r_P ⊣ R_P` be adjunctions out of `DX`,
* `adjQ : r_{VP} ⊣ R_{VP}` an adjunction from `DV` to `DP`,
* `adjShV : sh_V ⊣ r_V` an adjunction exhibiting `sh_V` as a left adjoint of `r_V`,
* `cmpU : r_U ⋙ r_{UP} ≅ r_P` and `cmpV : r_V ⋙ r_{VP} ≅ r_P` identify the two iterated
  restrictions with the restriction to the overlap.

Suppose the counits of `adjU` and of `adjQ` are invertible, and that for every object `Z` of
`DV` whose restriction `r_{VP} Z` to the overlap vanishes,

* `r_U (R_V Z)` vanishes,
* `r_U (sh_V Z)` vanishes,
* the unit `Z ⟶ r_V (sh_V Z)` is invertible.

Then every datum of an object `A` of `DU`, an object `B` of `DV` and an isomorphism
`c : r_{UP} A ≅ r_{VP} B` is glued by an object `F` of `DX` together with isomorphisms
`f : r_U F ≅ A` and `g : r_V F ≅ B` inducing `c` on the overlap.

This is the source's own proof of the first assertion of Stacks 08HB, with the geometry
isolated into the three vanishing-and-invertibility hypotheses: `F` is the fibre of
`R_U A ⊕ R_V B ⟶ R_P(r_{VP} B)`, invertibility of `f` comes from
`CategoryTheory.isIso_map_fst_of_distinguished_triangle` applied to the `V`-component of that
map, which `CategoryTheory.adjoint_factor` and
`CategoryTheory.isIso_map_unit_of_kernel_le` exhibit as a unit map inverted by `r_U`, and
invertibility of `g` comes from
`CategoryTheory.isIso_of_isIso_map_of_bijective_comp_on_kernel`, whose bijectivity hypothesis
is the triangle read against `sh_V Z`. -/
theorem exists_glue_of_restrictionData
    {rU : DX ⥤ DU} {RU : DU ⥤ DX} (adjU : rU ⊣ RU)
    {rV : DX ⥤ DV} {RV : DV ⥤ DX} (adjV : rV ⊣ RV)
    {rP : DX ⥤ DP} {RP : DP ⥤ DX} (adjP : rP ⊣ RP)
    {rVP : DV ⥤ DP} {RVP : DP ⥤ DV} (adjQ : rVP ⊣ RVP)
    {shV : DV ⥤ DX} (adjShV : shV ⊣ rV)
    (rUP : DU ⥤ DP) (cmpU : rU ⋙ rUP ≅ rP) (cmpV : rV ⋙ rVP ≅ rP)
    [rU.Additive] [rU.CommShift ℤ] [rU.IsTriangulated]
    [rP.Additive] [rUP.Additive]
    [rVP.Additive] [rVP.CommShift ℤ] [rVP.IsTriangulated]
    [RV.Additive] [RV.CommShift ℤ] [RV.IsTriangulated] [RP.CommShift ℤ]
    (hcU : IsIso adjU.counit) (hcQ : IsIso adjQ.counit)
    (hvanPush : ∀ Z : DV, IsZero (rVP.obj Z) → IsZero (rU.obj (RV.obj Z)))
    (hvanShriek : ∀ Z : DV, IsZero (rVP.obj Z) → IsZero (rU.obj (shV.obj Z)))
    (hunit : ∀ Z : DV, IsZero (rVP.obj Z) → IsIso (adjShV.unit.app Z))
    (A : DU) (B : DV) (c : rUP.obj A ≅ rVP.obj B) :
    ∃ (F : DX) (f : rU.obj F ≅ A) (g : rV.obj F ≅ B),
      c.hom = rUP.map f.inv ≫ cmpU.hom.app F ≫ cmpV.inv.app F ≫ rVP.map g.hom := by
  have := hcU
  have := hcQ
  obtain ⟨F, u, v, δ, hT, hcompat⟩ :=
    exists_gluing_triangle rUP rVP adjU adjV adjP cmpU cmpV A B c
  let f := (adjU.homEquiv F A).symm u
  let g := (adjV.homEquiv F B).symm v
  suffices hIso : IsIso f ∧ IsIso g by
    have := hIso.1
    have := hIso.2
    refine ⟨F, asIso f, asIso g, ?_⟩
    change rUP.map f ≫ c.hom = cmpU.hom.app F ≫ cmpV.inv.app F ≫ rVP.map g at hcompat
    have hh := congrArg (fun t => rUP.map (inv f) ≫ t) hcompat
    simp only [← Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id] at hh
    rw [rUP.map_id] at hh
    simpa only [Category.id_comp, Category.assoc, asIso_inv, asIso_hom] using hh
  have hunitB : IsIso ((RV ⋙ rU).map (adjQ.unit.app B)) :=
    isIso_map_unit_of_kernel_le adjQ (RV ⋙ rU) hvanPush B
  let aV := adjP.homEquiv (RV.obj B) (rVP.obj B)
    (cmpV.inv.app (RV.obj B) ≫ rVP.map (adjV.counit.app B) ≫ 𝟙 _)
  have haV : IsIso (rU.map aV) := by
    dsimp only [aV]
    rw [Category.comp_id, adjoint_factor adjV adjQ adjP cmpV, rU.map_comp]
    have : IsIso (rU.map (RV.map (adjQ.unit.app B))) := hunitB
    infer_instance
  have hneg : IsIso (rU.map (-aV)) := by
    rw [rU.map_neg]
    exact (-asIso (rU.map aV)).isIso_hom
  have hu : IsIso (rU.map u) := by
    have h := isIso_map_fst_of_distinguished_triangle rU _ _ (-aV) δ hT
    have heq : biprod.lift u v ≫ biprod.fst = u := biprod.lift_fst u v
    rw [heq] at h
    exact h
  have hf : IsIso f := by
    change IsIso (rU.map u ≫ adjU.counit.app A)
    infer_instance
  refine ⟨hf, ?_⟩
  have hgP : IsIso (rVP.map g) := by
    change rUP.map f ≫ c.hom = cmpU.hom.app F ≫ cmpV.inv.app F ≫ rVP.map g at hcompat
    have : IsIso ((cmpU.hom.app F ≫ cmpV.inv.app F) ≫ rVP.map g) := by
      rw [Category.assoc, ← hcompat]
      infer_instance
    exact IsIso.of_isIso_comp_left (cmpU.hom.app F ≫ cmpV.inv.app F) (rVP.map g)
  apply isIso_of_isIso_map_of_bijective_comp_on_kernel rVP g
  intro Z hZ
  have hη : IsIso (adjShV.unit.app Z) := hunit Z hZ
  have hLU : IsZero (rU.obj (shV.obj Z)) := hvanShriek Z hZ
  have hH : IsZero (rP.obj (shV.obj Z)) :=
    (rUP.map_isZero hLU).of_iso (cmpU.app (shV.obj Z)).symm
  apply bijective_comp_of_adjunctions adjV adjShV Z v
  apply bijective_comp_snd_of_distinguished_triangle u v _ δ hT
  · exact hom_eq_zero_of_isZero_leftAdjoint adjU hLU
  · exact hom_eq_zero_of_isZero_leftAdjoint adjP hH
  · intro a
    let iW := (RP.commShiftIso (-1 : ℤ)).app (rVP.obj B)
    apply (cancel_mono iW.inv).1
    rw [zero_comp]
    exact hom_eq_zero_of_isZero_leftAdjoint adjP hH (a ≫ iW.inv)

end Glueing

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- The universe-polymorphic `Abelian` instance of `Stacks.Cohomology.SiteModules` leaves the
-- module universe of `AlgebraicGeometry.Space.Modules` undetermined; the instance of Mathlib is
-- the one used here.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

section OpenImmersion

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {U X : AlgebraicSpaces B S hS} (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)
  [HasSheafify (smallEtaleRingedSite B S hS U.1 U.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS U.1 U.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify (smallEtaleRingedSite B S hS U.1 U.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS U.1 U.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Restriction of modules along an open immersion is a left inverse of extension by zero.**
For an open immersion `j : U ⟶ X` of algebraic spaces the unit `M ⟶ (j_!M)|_U` of
`j_! ⊣ (-)|_U` is an isomorphism, since `j_! ⊣ (-)|_U ⊣ j_*` is an adjoint triple whose right
counit `(j_*M)|_U ⟶ M` is one. -/
theorem isIso_etaleModuleLowerShriekAdjunction_unit :
    IsIso (etaleModuleLowerShriekAdjunction B S hS j
      (isEtale_of_isOpenImmersion B S hS hj)).unit := by
  have hff := fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj
  have := hff.full
  have := hff.faithful
  exact (Adjunction.Triple.isIso_unit_iff_isIso_counit
    { adj₁ := etaleModuleLowerShriekAdjunction B S hS j (isEtale_of_isOpenImmersion B S hS hj)
      adj₂ := etaleModulePullbackAdjunction B S hS j
        (isEtale_of_isOpenImmersion B S hS hj) }).2 inferInstance

/-- The same on unbounded derived categories: for an open immersion the unit
`E ⟶ (j_!E)|_U` of the derived adjunction `j_! ⊣ (-)|_U` is an isomorphism. -/
theorem isIso_derivedEtaleModuleLowerShriekAdjunction_unit :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS j
      (isEtale_of_isOpenImmersion B S hS hj)).mapDerivedCategory).unit := by
  have h := isIso_etaleModuleLowerShriekAdjunction_unit B S hS j hj
  exact Stacks.Adjunction.isIso_unit_of_comp_iso_id _
    ((Functor.mapDerivedCategoryComp (etaleModuleLowerShriek B S hS j
        (isEtale_of_isOpenImmersion B S hS hj))
      (etaleModulePullback.{u, u} B S hS j (isEtale_of_isOpenImmersion B S hS hj))).symm ≪≫
      asIso (NatTrans.mapDerivedCategory (asIso (etaleModuleLowerShriekAdjunction B S hS j
        (isEtale_of_isOpenImmersion B S hS hj)).unit).inv) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- **The counit of a right adjoint of derived restriction along an open immersion is
invertible.**  Let `j : U ⟶ X` be an open immersion of algebraic spaces and let `R` be a right
adjoint of restriction on unbounded derived categories of modules.  Then the counit
`(R E)|_U ⟶ E` of that adjunction is an isomorphism.

Extension by zero, restriction and `R` form an adjoint triple, and the unit of its left half is
invertible by `AlgebraicGeometry.Space.isIso_derivedEtaleModuleLowerShriekAdjunction_unit`. -/
theorem isIso_counit_mapDerivedCategory_of_isOpenImmersion
    {R : DerivedCategory (Modules.{u, u} B S hS U.1 U.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2)}
    (adj : (etaleModulePullback.{u, u} B S hS j
      (isEtale_of_isOpenImmersion B S hS hj)).mapDerivedCategory ⊣ R) :
    IsIso adj.counit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    { adj₁ := (etaleModuleLowerShriekAdjunction B S hS j
        (isEtale_of_isOpenImmersion B S hS hj)).mapDerivedCategory
      adj₂ := adj }).1 (isIso_derivedEtaleModuleLowerShriekAdjunction_unit B S hS j hj)

end OpenImmersion

section Square

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The restriction to `U` of the extension by zero of an object of `D(𝒪_V)` vanishes if the
restriction of that object to the intersection does (Stacks 08HA). -/
private theorem isZero_restrictOpen_lowerShriek_of_isZero_edsRestrictSnd
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : IsZero ((edsRestrictSnd B S hS hsq).mapDerivedCategory.obj F)) :
    IsZero ((edsRestrictOpen B S hS hsq).mapDerivedCategory.obj
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F)) := by
  have hbc := isIso_derivedRestrictExtensionByZeroMap B S hS
    (isPullback_edsInter B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq))
    (etaleModuleLowerShriekAdjunction B S hS (edsFst B S hS hsq) (isEtale_edsFst B S hS hsq))
  exact ((etaleModuleLowerShriek B S hS (edsFst B S hS hsq)
      (isEtale_edsFst B S hS hsq)).mapDerivedCategory.map_isZero hF).of_iso
    ((asIso (derivedRestrictExtensionByZeroMap B S hS (isPullback_edsInter B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
      (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsFst B S hS hsq)
        (isEtale_edsFst B S hS hsq)))).app F).symm

/-- **The extension by zero of an object of `D(𝒪_V)` restricting to zero on the intersection is
supported on `T = |X| \ |U|`.**  Stacks 08HA at the cartesian square `P = U ×_X V` identifies
`(j_!F)|_U` with `p_!(F|_P)`, which vanishes. -/
theorem cohomologySupportedOn_lowerShriek_of_isZero_edsRestrictSnd
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : IsZero ((edsRestrictSnd B S hS hsq).mapDerivedCategory.obj F)) :
    CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo)
      ((etaleModuleLowerShriek B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj F) := by
  exact cohomologySupportedOn_compl_range_of_isZero_etaleModulePullback B S hS
    (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq) _
    (isZero_restrictOpen_lowerShriek_of_isZero_edsRestrictSnd B S hS hsq F hF)

/-- **The unit of extension by zero is invertible at an object restricting to zero on the
intersection.**  For `F` in `D(𝒪_V)` with `F|_P = 0` the unit `F ⟶ (j_!F)|_V` of the derived
adjunction of `AlgebraicGeometry.Space.etaleModuleLowerShriekAdjunction` is invertible: `j_!F`
is supported on `T`, so clause (1)(b) of Stacks 08GG inverts the counit there, the triangle
identity then inverts `j_!` of the unit, and `j_!` reflects isomorphisms. -/
theorem isIso_unit_mapDerivedCategory_lowerShriek_of_isZero_edsRestrictSnd
    (F : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hF : IsZero ((edsRestrictSnd B S hS hsq).mapDerivedCategory.obj F)) :
    IsIso ((etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.unit.app F) := by
  have hcounit := isIso_counit_derivedRestrict_of_cohomologySupportedOn B S hS hsq
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory _
    (cohomologySupportedOn_lowerShriek_of_isZero_edsRestrictSnd B S hS hsq F hF)
  have hmap := Adjunction.isIso_map_unit_app_of_isIso_counit_app
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory F
  exact isIso_of_isIso_mapDerivedCategory_map_leftAdjoint_etaleModulePullback B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)) _ hmap

/-- **The existence of the glued object.**  Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over a scheme `S`, let `P = U ×_X V` be its intersection
and write `(-)|_Y` for restriction along the étale morphism `j_Y : Y ⟶ X`.  Then an object `A` of
`D(𝒪_U)`, an object `Bo` of `D(𝒪_V)` and an isomorphism `c : A|_P ⟶ Bo|_P` are glued by an
object `F` of `D(𝒪_X)` together with isomorphisms `f : F|_U ⟶ A` and `g : F|_V ⟶ Bo` satisfying
`c = g|_P ∘ f^{-1}|_P`, which is the conclusion's equation.

`F` is the source's own object, the fibre of `Rj_{U,*}A ⊕ Rj_{V,*}Bo ⟶ Rj_{P,*}(Bo|_P)`; the
whole triangulated argument is `CategoryTheory.exists_glue_of_restrictionData`.  The two
vanishings for `Z|_P = 0` are both Stacks 08HA, at the two readings of the cartesian square
`P = U ×_X V`; the invertibility of the counits of `(-)|_U ⊣ Rj_{U,*}` and `(-)|_P ⊣ Rp_*` is
`AlgebraicGeometry.Space.isIso_counit_mapDerivedCategory_of_isOpenImmersion`, the open
immersions being `j_U` and its base change `P ⟶ V`; and the invertibility of the unit
`Z ⟶ (j_{V!}Z)|_V` for `Z|_P = 0` is
`AlgebraicGeometry.Space.isIso_unit_mapDerivedCategory_lowerShriek_of_isZero_edsRestrictSnd`.

The source's object `B` of `D(𝒪_V)` is written `Bo` here, the letter `B` being the big fppf
site. -/
theorem exists_glued_object
    (A : DerivedCategory
      (Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2))
    (Bo : DerivedCategory
      (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2))
    (c : (edsRestrictFst B S hS hsq).mapDerivedCategory.obj A ≅
      (edsRestrictSnd B S hS hsq).mapDerivedCategory.obj Bo) :
    ∃ (F : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
      (f : (edsRestrictOpen B S hS hsq).mapDerivedCategory.obj F ≅ A)
      (g : (edsRestrictEtale B S hS hsq).mapDerivedCategory.obj F ≅ Bo),
      c.hom = (edsRestrictFst B S hS hsq).mapDerivedCategory.map f.inv ≫
        (edsDerivedRestrictCompOpen B S hS hsq).hom.app F ≫
          (edsDerivedRestrictCompEtale B S hS hsq).inv.app F ≫
          (edsRestrictSnd B S hS hsq).mapDerivedCategory.map g.hom := by
  obtain ⟨RU, ⟨adjU⟩⟩ := nonempty_etaleModulePullback_mapDerivedCategory_adjunction B S hS
    (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
  obtain ⟨RV, ⟨adjV⟩⟩ := nonempty_etaleModulePullback_mapDerivedCategory_adjunction B S hS
    (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
  obtain ⟨RP, ⟨adjP⟩⟩ := nonempty_etaleModulePullback_mapDerivedCategory_adjunction B S hS
    (edsInterHom B S hS hsq) (isEtale_edsInterHom B S hS hsq)
  obtain ⟨RQ, ⟨adjQ⟩⟩ := nonempty_etaleModulePullback_mapDerivedCategory_adjunction B S hS
    (edsSnd B S hS hsq) (isEtale_edsSnd B S hS hsq)
  have : RV.Additive := adjV.right_adjoint_additive
  let : RV.CommShift ℤ := adjV.rightAdjointCommShift ℤ
  have := adjV.commShift_of_leftAdjoint ℤ
  have : RV.IsTriangulated := adjV.isTriangulated_rightAdjoint
  let : RP.CommShift ℤ := adjP.rightAdjointCommShift ℤ
  have hcOpen : IsIso adjU.counit :=
    isIso_counit_mapDerivedCategory_of_isOpenImmersion B S hS (edsOpenHom B S hS hsq)
      hsq.isOpenSubspace.2 _
  have hcSnd : IsIso adjQ.counit :=
    isIso_counit_mapDerivedCategory_of_isOpenImmersion B S hS (edsSnd B S hS hsq)
      (isOpenImmersion_of_isPullback B S hS (isPullback_edsInter B S hS hsq)
        hsq.isOpenSubspace.2) _
  have hvanPush : ∀ Z, IsZero ((edsRestrictSnd B S hS hsq).mapDerivedCategory.obj Z) →
      IsZero ((edsRestrictOpen B S hS hsq).mapDerivedCategory.obj (RV.obj Z)) := by
    intro Z hZ
    have hbc' := isIso_derivedRestrictExtensionByZeroMap B S hS
      (isPullback_edsInter B S hS hsq).flip (isEtale_edsOpenHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq))
      (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq))
    exact isZero_restrict_rightAdjoint_of_isZero_restrict
      (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory adjV
      (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
        (isEtale_edsSnd B S hS hsq)).mapDerivedCategory
      (asIso (derivedRestrictExtensionByZeroMap B S hS
        (isPullback_edsInter B S hS hsq).flip (isEtale_edsOpenHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)
        (etaleModuleLowerShriekAdjunction B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq))
        (etaleModuleLowerShriekAdjunction B S hS (edsSnd B S hS hsq)
          (isEtale_edsSnd B S hS hsq)))) hZ
  exact exists_glue_of_restrictionData adjU adjV adjP adjQ
    (etaleModuleLowerShriekAdjunction B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory
    (edsRestrictFst B S hS hsq).mapDerivedCategory
    (edsDerivedRestrictCompOpen B S hS hsq) (edsDerivedRestrictCompEtale B S hS hsq)
    hcOpen hcSnd hvanPush
    (isZero_restrictOpen_lowerShriek_of_isZero_edsRestrictSnd B S hS hsq)
    (isIso_unit_mapDerivedCategory_lowerShriek_of_isZero_edsRestrictSnd B S hS hsq) A Bo c

end Square

end AlgebraicGeometry.Space

end
