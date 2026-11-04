module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Final
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RanBaseChangeModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Equalizers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.CostructuredArrow
public import StacksFrontier.CategoryTheory.Functor.KanExtension.RanEvaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Base change for higher direct images along a 1-morphism of algebraic stacks

Let `S` be a scheme, let `τ` be a topology on the schemes of a big fppf site, and let

```
𝒴' ×_𝒴 𝒳 --- g' ---> 𝒳
   |                 |
   f'                f
   v                 v
  𝒴' ------ g -----> 𝒴
```

be the 2-cartesian square of a cospan `f : 𝒳 ⟶ 𝒴`, `g : 𝒴' ⟶ 𝒴` of algebraic stacks over `S`.
Stacks 075H says that the base change map `g⁻¹Rf_*ℱ ⟶ Rf'_*(g')⁻¹ℱ` is an isomorphism, functorially
in `ℱ`, both for abelian sheaves on `𝒳_τ` and for sheaves of `𝒪_𝒳`-modules; equivalently, that the
induced maps `g⁻¹Rⁱf_*ℱ ⟶ Rⁱf'_*((g')⁻¹ℱ)` are isomorphisms for every `i`.

The proof is the source's. In degree zero the isomorphism is Stacks 075B, the Guitart exactness of
the 2-fibre product square, which identifies `g⁻¹f_*` with `f'_*(g')⁻¹` on underlying presheaves;
for sheaves of modules the identification is moreover linear. Since `g⁻¹` is exact,
`g⁻¹ ∘ Rⁱf_*` is the `i`-th derived functor of `g⁻¹ ∘ f_* = f'_* ∘ (g')⁻¹`, and since `(g')⁻¹` is
exact and carries injectives to `f'_*`-acyclic objects, that is `Rⁱf'_* ∘ (g')⁻¹`. The
acyclicity is where the source uses Stacks 075G: `Rⁱf'_*` is the sheafification of the presheaf
`y' ↦ Hⁱ` of the fibre of `f'` over `y'`, and the fibre of `f'` over `y'` maps faithfully to `𝒳`,
so the restriction of `(g')⁻¹I` to it, for `I` injective, is injective by Stacks 06X1 (Stacks 06X2
for modules).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.abelianHigherDirectImageBaseChangeIso`: **Stacks 075H**
  for abelian sheaves.
* `AlgebraicGeometry.Stack.AlgebraicStacks.moduleHigherDirectImageBaseChangeIso`: **Stacks 075H**
  for sheaves of modules.
* `AlgebraicGeometry.Stack.moduleSheafPushforwardBaseChangeIso`: Stacks 075B for direct images of
  sheaves of modules, `f_* ⋙ g^* ≅ (g')^* ⋙ f'_*`.
* `AlgebraicGeometry.Stack.isZero_rightDerived_sheafPushforwardCocontinuous_snd_obj` and
  `AlgebraicGeometry.Stack.isZero_rightDerived_moduleSheafPushforward_snd_obj`: `(g')⁻¹` carries
  injectives to `f'_*`-acyclic objects.

## Implementation notes

The fibre of `f'` over an object `y'` of `𝒴'` is taken to be the comma category
`CostructuredArrow f' y'` of pairs `(x', f'(x') ⟶ y')`, with the topology it inherits as a category
over the big fppf category of `S`; it is fibred in groupoids, and it is equivalent to the source's
`(Sch/V)_{fppf} ×_{y', 𝒴'} 𝒳'`. It is the category over which the right Kan extension computing
`f'_*` is a limit, so the sections of `f'_*` over `y'` are its global sections on the nose. Its
projection to `𝒳'` is faithful, and so is its composite with `g'`, because `𝒴'` is fibred in
groupoids; it has equalizers because `𝒳'` does, being an algebraic stack (Stacks 04T2, 06WY).

The statements are per degree: for each `i`, a natural isomorphism of functors
`Rⁱf_* ⋙ g⁻¹ ≅ (g')⁻¹ ⋙ Rⁱf'_*`, which is the form the source's proof concludes with.

The source restricts `τ` to the Zariski, étale, smooth, syntomic and fppf topologies. The abelian
statement holds for every topology on the schemes of the big fppf site and the module statement for
every topology coarser than the fppf topology, which is what makes the structure presheaves
sheaves; the five topologies of the source are among these. The coefficients are abelian groups,
respectively modules, in any universe containing the one of the schemes, which is the size
condition under which the direct images and the injective resolutions exist.

## References

* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
* [Stacks Project, Tag 075G](https://stacks.math.columbia.edu/tag/075G)
* [Stacks Project, Tag 06X1](https://stacks.math.columbia.edu/tag/06X1)
* [Stacks Project, Tag 06X2](https://stacks.math.columbia.edu/tag/06X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

/-- For the 2-fibre product `𝒳 ×_𝒮 𝒴` over `𝒞` with `𝒴` fibred in groupoids and an object `y`
of `𝒴`, the functor from the costructured arrows `(P, P.y ⟶ y)` of the second projection to `𝒳`
is faithful: a morphism is determined by its `𝒳`-component, since its `𝒴`-component is then the
unique lift through `P'.y ⟶ y` of the base morphism it lies over. -/
theorem faithful_costructuredArrowProj_comp_fst (h𝒴 : p𝒴.IsFiberedInGroupoids) (y : 𝒴) :
    (CostructuredArrow.proj (snd p𝒳 p𝒴 p𝒮 F G) y ⋙ fst p𝒳 p𝒴 p𝒮 F G).Faithful where
  map_injective {e e'} h h' hh := by
    have ha : h.left.a = h'.left.a := hh
    have hbase : h.left.hbase = h'.left.hbase := by rw [Hom.hbase_eq, Hom.hbase_eq, ha]
    have hb₁ := h.left.hb
    have hb₂ : p𝒴.IsHomLift h.left.hbase h'.left.b := by rw [hbase]; exact h'.left.hb
    have key : p𝒴.map h.left.b = p𝒴.map h'.left.b := by
      rw [IsHomLift.fac' p𝒴 h.left.hbase h.left.b, IsHomLift.fac' p𝒴 h.left.hbase h'.left.b]
    have w₁ : h.left.b ≫ e'.hom = e.hom := CostructuredArrow.w h
    obtain ⟨χ, -, huniq⟩ := h𝒴.unique_lift e'.hom e.hom (p𝒴.map h.left.b)
      ((p𝒴.map_comp _ _).symm.trans (congrArg p𝒴.map w₁))
    exact CostructuredArrow.hom_ext _ _ (Hom.ext' ha
      ((huniq _ ⟨rfl, w₁⟩).trans (huniq _ ⟨key.symm, CostructuredArrow.w h'⟩).symm))

end CategoryTheory.TwoFibreProductOver

namespace CategoryTheory.Functor

/-- The value at `y` of a right Kan extension along `L.op` is the limit of the restriction to
the opposite of the category of costructured arrows `(c, L c ⟶ y)`, naturally in the functor
extended. -/
noncomputable def ranOpObjIsoLimCostructuredArrow {C D H : Type*} [Category* C] [Category* D]
    [Category* H] (L : C ⥤ D) [∀ F : Cᵒᵖ ⥤ H, L.op.HasPointwiseRightKanExtension F] (y : D)
    [HasLimitsOfShape (StructuredArrow (op y) L.op) H]
    [HasLimitsOfShape (CostructuredArrow L y)ᵒᵖ H] :
    L.op.ran ⋙ (evaluation Dᵒᵖ H).obj (op y) ≅
      (Functor.whiskeringLeft _ _ H).obj (CostructuredArrow.proj L y).op ⋙ lim :=
  ranObjNatIsoLimit H L.op (op y) ≪≫
    isoWhiskerLeft _ (Initial.limIso (costructuredArrowOpEquivalence L y).functor).symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u a

attribute [local instance] hasSheafify_associatedTopology_of_essentiallySmall

/-- Abelian sheaves on the site associated with a category over the big fppf category of `S`,
whose objects and morphisms live in the universes of the schemes, have enough injectives: the
site is essentially small and abelian sheaves on it form a Grothendieck abelian category. -/
instance enoughInjectives_sheaf_associatedTopology (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒵 : Type (u + 1)} [Category.{u} 𝒵] (p : 𝒵 ⥤ BigFppfOver B S hS)
    (τ : GrothendieckTopology B.Schemes) :
    EnoughInjectives
      (Sheaf (associatedTopology B S hS p τ) AddCommGrpCat.{max (u + 1) a}) :=
  (Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) a}
    (associatedTopology B S hS p τ) AddCommGrpCat.{max (u + 1) a}).enoughInjectives

section Acyclic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴' : Type (u + 1)} [Category.{u} 𝒴']
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes)


/-- The value at `y'` of a higher right derived functor of `K ⋙ f'_*` vanishes on `J` if `P` is
exact, preserves injectives, sends `J` to an injective object, and restricting `K J` to the fibre
of `f'` over `y'` is `K' (P J)`. -/
private theorem isZero_rightDerived_ran_obj_of_injective
    {X Z : Type*} [Category* X] [Category* Z] [Abelian X] [Abelian Z] [EnoughInjectives X]
    [EnoughInjectives Z] {X' Y' : Type (u + 1)} [Category.{u} X'] [Category.{u} Y']
    (f' : X' ⥤ Y') (y' : Y') (K : X ⥤ X'ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a})
    (K' : Z ⥤ (CostructuredArrow f' y')ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a})
    [(K ⋙ f'.op.ran).Additive] [K'.Additive] (P : X ⥤ Z) [P.Additive] [P.PreservesHomology]
    [P.PreservesInjectiveObjects]
    (ε : P ⋙ K' ≅ K ⋙ (Functor.whiskeringLeft _ _ _).obj (CostructuredArrow.proj f' y').op)
    (J : X) [Injective (P.obj J)] (n : ℕ) (hn : 0 < n) :
    IsZero ((((K ⋙ f'.op.ran).rightDerived n).obj J).obj (op y')) := by
  let : (lim : ((CostructuredArrow f' y')ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a}) ⥤ _).Additive :=
    Functor.additive_of_preserves_binary_products _
  let ev := (evaluation Y'ᵒᵖ AddCommGrpCat.{max (u + 1) a}).obj (op y')
  have e₁ : (K ⋙ f'.op.ran) ⋙ ev ≅ P ⋙ K' ⋙ lim :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft K (Functor.ranOpObjIsoLimCostructuredArrow f' y') ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ε.symm lim ≪≫
      Functor.associator _ _ _
  refine IsZero.of_iso ?_ ((Functor.rightDerivedCompIso (K ⋙ f'.op.ran) ev n).app J).symm
  refine IsZero.of_iso ?_ ((Functor.rightDerivedIsoOfNatIso e₁ n).app J)
  refine IsZero.of_iso ?_
    (Functor.rightDerivedCompIsoOfPreservesInjectiveObjects P (K' ⋙ lim) J n)
  exact Stacks.RightDerivedComp.isZero_rightDerived_obj_of_injective _ _ n hn


/-- **The inverse image `(g')⁻¹` carries injective abelian sheaves to `f'_*`-acyclic ones.** For
the canonical 2-cartesian square of categories fibred in groupoids over the big fppf category of
`S` whose apex has equalizers, and an injective abelian sheaf `I` on `𝒳`,
`Rⁿf'_*((g')⁻¹I) = 0` for `n > 0`.

`Rⁿf'_*` is the sheafification of the derived presheaf direct image (Stacks 075G), whose value at
`y'` is the `n`-th derived functor of the sections over the fibre `CostructuredArrow f' y'` of the
restriction. Restriction to the fibre is exact and preserves injectives (Stacks 06X1), so that
derived functor is the cohomology of the fibre with coefficients in the restriction of
`(g')⁻¹I`; and that restriction is the restriction of `I` along the composite of the fibre with
`g'`, which is faithful, so it is injective (Stacks 06X1 again) and its higher cohomology
vanishes. -/
theorem isZero_rightDerived_sheafPushforwardCocontinuous_snd_obj
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [HasEqualizers (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)]
    (I : Sheaf (associatedTopology B S hS p𝒳 τ) AddCommGrpCat.{max (u + 1) a}) [Injective I]
    (n : ℕ) (hn : 0 < n) :
    letI : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
      isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
    letI : p𝒳.IsFibered := h𝒳.isFibered
    letI : p𝒴'.IsFibered := h𝒴'.isFibered
    letI := isContinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ h𝒳 TwoFibreProductOver.fst_comp_eq
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ h𝒴' TwoFibreProductOver.snd_comp_eq
    letI : ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒴' τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ
        (h𝒴'.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq)
    IsZero ((((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒴' τ)).rightDerived n).obj
      (((TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒳 τ)).obj I)) := by
  let pX' := TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g
  let g' := TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g
  let f' := TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g
  let A := AddCommGrpCat.{max (u + 1) a}
  let JX := associatedTopology B S hS p𝒳 τ
  let JX' := associatedTopology B S hS pX' τ
  have hX' : pX'.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let : pX'.IsFibered := hX'.isFibered
  let : p𝒳.IsFibered := h𝒳.isFibered
  let : p𝒴'.IsFibered := h𝒴'.isFibered
  let := isContinuous_of_isFiberedInGroupoids B S hS pX' p𝒳 g' τ h𝒳
    TwoFibreProductOver.fst_comp_eq
  let := isCocontinuous_of_isFiberedInGroupoids B S hS pX' p𝒴' f' τ h𝒴'
    TwoFibreProductOver.snd_comp_eq
  let J := (g'.sheafPushforwardContinuous A JX' JX).obj I
  refine IsZero.of_iso ?_ ((derivedDirectImageIsoSheafifyDerivedPresheafDirectImage B S hS pX'
    p𝒴' f' τ (h𝒴'.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq) n).app J)
  refine Functor.map_isZero (presheafToSheaf (associatedTopology B S hS p𝒴' τ) A)
    (X := (derivedPresheafDirectImage B S hS pX' f' τ n).obj J) (Functor.isZero _ fun y => ?_)
  obtain ⟨y'⟩ := y
  -- the fibre of `f'` over `y'`
  let π := CostructuredArrow.proj f' y'
  let pE := π ⋙ pX'
  have hE : pE.IsFiberedInGroupoids :=
    (Functor.IsFiberedInGroupoids.costructuredArrow_proj f' y').comp _ _ hX'
  let : pE.IsFibered := hE.isFibered
  let JE := associatedTopology B S hS pE τ
  have hπg : (π ⋙ g') ⋙ p𝒳 = pE := by
    show π ⋙ (g' ⋙ p𝒳) = π ⋙ pX'
    rw [TwoFibreProductOver.fst_comp_eq]
  let := isContinuous_of_isFiberedInGroupoids B S hS pE pX' π τ hX' rfl
  let : (π ⋙ g').Faithful :=
    TwoFibreProductOver.faithful_costructuredArrowProj_comp_fst p𝒳 p𝒴' p𝒴 f g h𝒴' y'
  let P := π.sheafPushforwardContinuous A JE JX'
  let : P.Additive := additive_sheafPushforwardContinuous B S hS pE pX' π τ
    (hX'.isFibredOneMorphism rfl)
  let : ∀ G : (CostructuredArrow f' y')ᵒᵖ ⥤ A, π.op.HasPointwiseRightKanExtension G :=
    fun G => Functor.hasPointwiseRightKanExtension_of_hasLimitsOfSize _ _
  let : P.PreservesHomology :=
    preservesHomology_sheafPushforwardContinuous.{u, u + 1, u + 1, u, u, max (u + 1) a}
      B S hS pE pX' π τ (hX'.isFibredOneMorphism rfl)
  let : P.PreservesInjectiveObjects := ⟨fun {K} hK => by
    let := hK
    exact injective_sheafPushforwardContinuous_obj B S hS pE pX' π τ hE hX' rfl K⟩
  have hinj : Injective (P.obj J) :=
    injective_sheafPushforwardContinuous_obj B S hS pE p𝒳 (π ⋙ g') τ hE h𝒳 hπg I
  let : (sheafToPresheaf JX' A ⋙ f'.op.ran).Additive := by
    let := (f'.op.ranAdjunction A).right_adjoint_additive
    infer_instance
  exact isZero_rightDerived_ran_obj_of_injective f' y' (sheafToPresheaf JX' A)
    (sheafToPresheaf JE A) P (Functor.sheafPushforwardContinuousCompSheafToPresheafIso π A JE JX')
    J n hn

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Base change for higher direct images of abelian sheaves.** For the canonical 2-cartesian
square of categories fibred in groupoids over the big fppf category of `S` whose apex has
equalizers, and any topology `τ`, `Rⁿf_* ⋙ g⁻¹ ≅ (g')⁻¹ ⋙ Rⁿf'_*` for every `n`.

The degree-zero isomorphism is `AlgebraicGeometry.Stack.abelianDirectImageBaseChangeIso`
(Stacks 075B); since `g⁻¹` is exact it identifies `(Rⁿf_*) ⋙ g⁻¹` with the derived functor of the
composite `(g')⁻¹ ⋙ f'_*` (`AlgebraicGeometry.Stack.abelianHigherDirectImageBaseChangeIso`), and
since `(g')⁻¹` is exact and carries injectives to `f'_*`-acyclic sheaves
(`isZero_rightDerived_sheafPushforwardCocontinuous_snd_obj`) the derived functor of that composite
is `(g')⁻¹ ⋙ Rⁿf'_*`. -/
noncomputable def abelianHigherDirectImageBaseChangeIsoOfHasEqualizers
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [HasEqualizers (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)] (n : ℕ) :
    letI : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
      isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
    letI : p𝒳.IsFibered := h𝒳.isFibered
    letI : p𝒴'.IsFibered := h𝒴'.isFibered
    letI : p𝒴.IsFibered := h𝒴.isFibered
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS p𝒳 p𝒴 f τ h𝒴 hfc
    letI := isContinuous_of_isFiberedInGroupoids B S hS p𝒴' p𝒴 g τ h𝒴 hgc
    letI := isContinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ h𝒳 TwoFibreProductOver.fst_comp_eq
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ h𝒴' TwoFibreProductOver.snd_comp_eq
    letI : (f.sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS p𝒳 p𝒴 f τ (h𝒴.isFibredOneMorphism hfc)
    letI : ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒴' τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ
        (h𝒴'.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq)
    (f.sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a}
            (associatedTopology B S hS p𝒳 τ)
            (associatedTopology B S hS p𝒴 τ)).rightDerived n ⋙
        g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS p𝒴' τ) (associatedTopology B S hS p𝒴 τ) ≅
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
          (associatedTopology B S hS p𝒳 τ) ⋙
        ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
            AddCommGrpCat.{max (u + 1) a}
            (associatedTopology B S hS
              (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
            (associatedTopology B S hS p𝒴' τ)).rightDerived n := by
  let pX' := TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g
  let g' := TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g
  let f' := TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g
  let A := AddCommGrpCat.{max (u + 1) a}
  let JX := associatedTopology B S hS p𝒳 τ
  let JX' := associatedTopology B S hS pX' τ
  let JY' := associatedTopology B S hS p𝒴' τ
  have hX' : pX'.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let : pX'.IsFibered := hX'.isFibered
  let : p𝒳.IsFibered := h𝒳.isFibered
  let : p𝒴'.IsFibered := h𝒴'.isFibered
  let : p𝒴.IsFibered := h𝒴.isFibered
  let hprX := h𝒳.isFibredOneMorphism
    (TwoFibreProductOver.fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  let hprY := h𝒴'.isFibredOneMorphism
    (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  let := (hprX.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hprX.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let := (hprY.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hprY.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let F := g'.sheafPushforwardContinuous A JX' JX
  let G := f'.sheafPushforwardCocontinuous A JX' JY'
  let : F.Additive := additive_sheafPushforwardContinuous B S hS pX' p𝒳 g' τ hprX
  let : G.Additive := additive_sheafPushforwardCocontinuous B S hS pX' p𝒴' f' τ hprY
  let : PreservesFiniteLimits F := hprX.preservesFiniteLimits_inverseImage
    (J := τ.over (B.obj hS)) (A := A)
  let := (hprX.sheafAdjunctionInheritedTopology (τ.over (B.obj hS)) A).leftAdjoint_preservesColimits
  let := (hprY.sheafAdjunctionInheritedTopology (τ.over (B.obj hS)) A).rightAdjoint_preservesLimits
  let : PreservesFiniteColimits F := inferInstance
  let : PreservesFiniteLimits G := inferInstance
  -- Acyclicity is phrased through derived categories; any models serve, and these are local.
  letI := HasDerivedCategory.standard (Sheaf JX' A)
  letI := HasDerivedCategory.standard (Sheaf JY' A)
  have hac : ∀ I : Sheaf JX A, Injective I → G.rightAcyclic (F.obj I) := fun I hI => by
    let := hI
    refine (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic G (F.obj I)).2 fun m hm => ?_
    exact isZero_rightDerived_sheafPushforwardCocontinuous_snd_obj B S hS p𝒳 p𝒴' p𝒴 f g τ h𝒳 h𝒴' h𝒴
      hfc hgc I m hm
  exact abelianHigherDirectImageBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g τ h𝒳 h𝒴' h𝒴 hfc hgc n ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic F G hac n

end Acyclic

section ModuleLegs

universe v w m v' w'

variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D] (L : C ⥤ D)
  (R : Dᵒᵖ ⥤ RingCat.{u})

/-- The module structure of the compatible-sections direct image of presheaves of modules of
Stacks 06WD, read on the legs of the right Kan extension: a section `r` over `y` acts on the leg
at `(x, y ⟶ L x)` through its restriction to `x`. -/
theorem moduleDirectImageData_leg_smul (T : Cᵒᵖ ⥤ RingCat.{u}) (h : T = L.op ⋙ R)
    (M : PresheafOfModules.{max u v w m v' w'} T) (y : Dᵒᵖ) (j : StructuredArrow y L.op)
    (r : R.obj y) (s : ((moduleDirectImageData.{u, v, w, m} L R T h).1.obj M).obj y) :
    Stacks.SheafOfModules.ranπ L.op M.presheaf y j
        (((moduleDirectImageData.{u, v, w, m} L R T h).2.1.hom.app M).app y (r • s)) =
      (eqToHom h.symm).app j.right (R.map j.hom r) •
        (show M.obj j.right from Stacks.SheafOfModules.ranπ L.op M.presheaf y j
          (((moduleDirectImageData.{u, v, w, m} L R T h).2.1.hom.app M).app y s)) := by
  subst h
  have key : ∀ t : compatibleSections.{v, w, max u v w m v' w'} L.op M.presheaf y,
      (((sectionsFunctorRanIso.{v, w, v', w', max u m} L.op).hom.app M.presheaf).app y ≫
        Stacks.SheafOfModules.ranπ L.op M.presheaf y j) t = t.val j.right (j.hom ≫ 𝟙 _) := by
    intro t
    rw [sectionsFunctorRanIso_hom_app_comp_ranπ]
    rfl
  refine (key (r • s)).trans ?_
  refine Eq.trans ?_ (congrArg _ (key s).symm)
  simp only [Category.comp_id]
  rfl

end ModuleLegs


section GenericScalar

universe v₀ w₀ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄ vD wD

variable {𝒞 : Type v₀} [Category.{w₀} 𝒞] {D : Type vD} [Category.{wD} D] (O : 𝒞ᵒᵖ ⥤ D)
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴 : Type v₂} [Category.{w₂} 𝒴]
  {𝒴' : Type v₃} [Category.{w₃} 𝒴'] {𝒳' : Type v₄} [Category.{w₄} 𝒳']
  {f : 𝒳 ⥤ 𝒴} {g : 𝒴' ⥤ 𝒴} {f' : 𝒳' ⥤ 𝒴'} {g' : 𝒳' ⥤ 𝒳} (w : TwoSquare g' f' f g)
  {pX : 𝒳 ⥤ 𝒞} {pY : 𝒴 ⥤ 𝒞} {pY' : 𝒴' ⥤ 𝒞} {pX' : 𝒳' ⥤ 𝒞}

omit [Category.{w₂} 𝒴] [Category.{w₃} 𝒴'] [Category.{w₄} 𝒳'] in
/-- An identification of two presheaves pulled back from a presheaf `O` along functors which
agree on objects is `O` applied to the identification of the base objects. -/
theorem eqToHom_app_op_comp_eq_map {𝒜 : Type v₁} [Category.{w₁} 𝒜] {ℬ : Type v₂}
    [Category.{w₂} ℬ] {F : 𝒜 ⥤ 𝒞} {G : 𝒜 ⥤ ℬ} {H : ℬ ⥤ 𝒞}
    (h : F.op ⋙ O = G.op ⋙ (H.op ⋙ O)) (e : ∀ X, F.obj X = H.obj (G.obj X)) (X : 𝒜ᵒᵖ) :
    (eqToHom h).app X = O.map (eqToHom (congrArg op (e X.unop))) :=
  (eqToHom_app h X).trans (eqToHom_map O (congrArg op (e X.unop))).symm

omit [Category.{w₂} 𝒴] [Category.{w₃} 𝒴'] [Category.{w₄} 𝒳'] in
/-- The reverse form of `eqToHom_app_op_comp_eq_map`. -/
theorem eqToHom_app_op_comp_eq_map_symm {𝒜 : Type v₁} [Category.{w₁} 𝒜] {ℬ : Type v₂}
    [Category.{w₂} ℬ] {F : 𝒜 ⥤ 𝒞} {G : 𝒜 ⥤ ℬ} {H : ℬ ⥤ 𝒞}
    (h : G.op ⋙ (H.op ⋙ O) = F.op ⋙ O) (e : ∀ X, H.obj (G.obj X) = F.obj X) (X : 𝒜ᵒᵖ) :
    (eqToHom h).app X = O.map (eqToHom (congrArg op (e X.unop))) :=
  (eqToHom_app h X).trans (eqToHom_map O (congrArg op (e X.unop))).symm

/-- The scalar identity behind the linearity of base change for direct images of modules: for
presheaves of rings pulled back from a common presheaf `O` along structure functors, and a
`2`-cell lying over identities, restricting a section along `y ⟶ g(f' x') ⟶ f(g' x')` agrees with
restricting it along `y ⟶ f' x'`, up to the identifications of the four presheaves of rings. -/
theorem pullbackPresheaf_baseChange_scalar
    (e₃ : ∀ x', pY.obj (g.obj (f'.obj x')) = pX'.obj x')
    (e₄ : ∀ x', pX'.obj x' = pY.obj (f.obj (g'.obj x')))
    (hψ : ∀ x', pY.IsHomLift (𝟙 (pX'.obj x')) (w.natTrans.app x'))
    (hf : (f ⋙ pY).op ⋙ O = f.op ⋙ (pY.op ⋙ O)) (hg : (g ⋙ pY).op ⋙ O = g.op ⋙ (pY.op ⋙ O))
    (hf' : pX'.op ⋙ O = f'.op ⋙ ((g ⋙ pY).op ⋙ O))
    (hg' : pX'.op ⋙ O = g'.op ⋙ ((f ⋙ pY).op ⋙ O))
    (y : 𝒴'ᵒᵖ) (j : StructuredArrow y f'.op) :
    (eqToHom hg).app y ≫ (pY.op ⋙ O).map (g.op.map j.hom ≫ w.op.natTrans.app j.right) ≫
        (eqToHom hf.symm).app (g'.op.obj j.right) =
      ((g ⋙ pY).op ⋙ O).map j.hom ≫ (eqToHom hf'.symm).app j.right ≫
        (eqToHom hg').app j.right := by
  rw [eqToHom_app_op_comp_eq_map O hg (fun _ => rfl),
    eqToHom_app_op_comp_eq_map_symm O hf.symm (fun _ => rfl),
    eqToHom_app_op_comp_eq_map_symm O hf'.symm e₃,
    eqToHom_app_op_comp_eq_map O hg' e₄]
  have hψ' := hψ j.right.unop
  have hn : w.op.natTrans.app j.right = (w.natTrans.app j.right.unop).op := rfl
  rw [hn]
  simp only [Functor.comp_map, ← O.map_comp]
  congr 1
  have key : pY.map (w.natTrans.app j.right.unop) =
      eqToHom ((e₄ _).symm.trans (e₃ _).symm) := by
    rw [IsHomLift.fac' pY (𝟙 (pX'.obj j.right.unop)) (w.natTrans.app j.right.unop)]
    simp
  apply Quiver.Hom.unop_inj
  simp only [Functor.op_map, unop_comp, Quiver.Hom.unop_op, Functor.map_comp, key, eqToHom_unop,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc, Functor.comp_map]
  simp

/-- `pullbackPresheaf_baseChange_scalar` for presheaves of rings that are only equal to the
pulled-back ones. -/
theorem pullbackPresheaf_baseChange_scalar_of_eq
    (hfc : f ⋙ pY = pX) (hgc : g ⋙ pY = pY')
    (e₃ : ∀ x', pY'.obj (f'.obj x') = pX'.obj x')
    (e₄ : ∀ x', pX'.obj x' = pX.obj (g'.obj x'))
    (hψ : ∀ x', pY.IsHomLift (𝟙 (pX'.obj x')) (w.natTrans.app x'))
    {RX : 𝒳ᵒᵖ ⥤ D} {RY : 𝒴ᵒᵖ ⥤ D} {RY' : 𝒴'ᵒᵖ ⥤ D} {RX' : 𝒳'ᵒᵖ ⥤ D}
    (hRX : RX = pX.op ⋙ O) (hRY : RY = pY.op ⋙ O) (hRY' : RY' = pY'.op ⋙ O)
    (hRX' : RX' = pX'.op ⋙ O)
    (hf : RX = f.op ⋙ RY) (hg : RY' = g.op ⋙ RY)
    (hf' : RX' = f'.op ⋙ RY') (hg' : RX' = g'.op ⋙ RX)
    (y : 𝒴'ᵒᵖ) (j : StructuredArrow y f'.op) :
    (eqToHom hg).app y ≫ RY.map (g.op.map j.hom ≫ w.op.natTrans.app j.right) ≫
        (eqToHom hf.symm).app (g'.op.obj j.right) =
      RY'.map j.hom ≫ (eqToHom hf'.symm).app j.right ≫ (eqToHom hg').app j.right := by
  subst hRX hRY hRY' hRX' hfc hgc
  exact pullbackPresheaf_baseChange_scalar O w e₃ e₄ hψ hf hg hf' hg' y j

end GenericScalar


section ModuleLinear

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴' : Type (u + 1)} [Category.{u} 𝒴']
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

omit [Category.{u} 𝒴'] in
/-- The module structure of the direct image of sheaves of modules of Stacks 06WE, read on the
legs of the right Kan extension computing its underlying abelian presheaf. -/
theorem moduleSheafPushforward_leg_smul (hp : p𝒳.IsFiberedInGroupoids)
    (hq : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)
    (M : SheafOfModules.{max (u + 1) a} (ringStructureSheafCore B S hS p𝒳 hp τ hτ)) (y : 𝒴ᵒᵖ)
    (j : StructuredArrow y f.op) (r : (ringStructureSheafCore B S hS p𝒴 hq τ hτ).obj.obj y)
    (s : ((moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS p𝒳 p𝒴 hp hq f hf τ
      hτ).obj M).val.obj y) :
    Stacks.SheafOfModules.ranπ f.op M.val.presheaf y j
        (((moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, max (u + 1) a}
          B S hS p𝒳 p𝒴 hp hq f hf τ hτ).hom.app M).app y (r • s)) =
      (eqToHom (ringStructureSheafCore_obj_eq B S hS p𝒳 p𝒴 hp hq f hf τ hτ).symm).app j.right
          ((ringStructureSheafCore B S hS p𝒴 hq τ hτ).obj.map j.hom r) •
        (show M.val.obj j.right from Stacks.SheafOfModules.ranπ f.op M.val.presheaf y j
          (((moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, max (u + 1) a}
            B S hS p𝒳 p𝒴 hp hq f hf τ hτ).hom.app M).app y s)) :=
  moduleDirectImageData_leg_smul.{u, u + 1, u, max (u + 1) a, u + 1, u} f
    (ringStructureSheafCore B S hS p𝒴 hq B.topology le_rfl).obj
    (ringStructureSheafCore B S hS p𝒳 hp B.topology le_rfl).obj
    (ringStructureSheafCore_obj_eq B S hS p𝒳 p𝒴 hp hq f hf B.topology le_rfl) M.val y j r s

/-- The structure sheaves of the canonical 2-cartesian square are compatible with its `2`-cell
on the legs of the right Kan extensions: the scalar identity that makes base change of direct
images of sheaves of modules linear. -/
theorem structureSheaf_baseChange_scalar
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    (y : 𝒴'ᵒᵖ) (j : StructuredArrow y (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op)
    (r : (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ).obj.obj y) :
    (eqToHom (ringStructureSheafCore_obj_eq B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ).symm).app
        ((TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).op.obj j.right)
        ((ringStructureSheafCore B S hS p𝒴 h𝒴 τ hτ).obj.map (g.op.map j.hom ≫
          (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).op.natTrans.app j.right)
          ((eqToHom (ringStructureSheafCore_obj_eq B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ)).app y r)) =
      (eqToHom (ringStructureSheafCore_obj_eq B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq τ hτ)).app
        j.right
        ((eqToHom (ringStructureSheafCore_obj_eq B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
          (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ
            hτ).symm).app j.right
          ((ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ).obj.map j.hom r)) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply]
  congr 1
  congr 1
  exact pullbackPresheaf_baseChange_scalar_of_eq
    (BigFppfOver.structureSheaf B S hS).obj (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g)
    (pX' := TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) hfc hgc
    (fun x' => x'.hy) (fun x' => x'.hx.symm)
    (fun x' => TwoFibreProductOver.psiIso_hom_vertical x')
    (ringStructureSheafCore_obj B S hS p𝒳 h𝒳 τ hτ)
    (ringStructureSheafCore_obj B S hS p𝒴 h𝒴 τ hτ)
    (ringStructureSheafCore_obj B S hS p𝒴' h𝒴' τ hτ)
    (ringStructureSheafCore_obj B S hS _ _ τ hτ)
    (ringStructureSheafCore_obj_eq B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
    (ringStructureSheafCore_obj_eq B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ)
    (ringStructureSheafCore_obj_eq B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ)
    (ringStructureSheafCore_obj_eq B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq τ hτ) y j

/-- **Base change for direct images of sheaves of modules in degree zero** (Stacks 075B at
module coefficients). For the canonical 2-cartesian square of categories fibred in groupoids over
the big fppf category of `S` and any topology `τ` coarser than the fppf topology,
`f_* ⋙ g^* ≅ (g')^* ⋙ f'_*` on sheaves of modules over the structure sheaves.

On underlying abelian presheaves it is the base change of right Kan extensions of
`AlgebraicGeometry.Stack.abelianPresheafBaseChangeIso`, which is invertible since the square is
Guitart exact; it is linear by `structureSheaf_baseChange_scalar`
(`Stacks.SheafOfModules.directImageBaseChange`). -/
noncomputable def moduleSheafPushforwardBaseChangeIso
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') :
    moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ ⋙
        modulePullback B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ ≅
      modulePullback B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq τ hτ ⋙
        moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
          (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ :=
  letI : p𝒴'.IsFibered := h𝒴'.isFibered
  letI : p𝒴.IsFibered := h𝒴.isFibered
  letI : p𝒳.IsFibered := h𝒳.isFibered
  letI : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
    isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  letI := isContinuous_of_isFiberedInGroupoids B S hS p𝒴' p𝒴 g τ h𝒴 hgc
  letI := isContinuous_of_isFiberedInGroupoids B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ h𝒳 TwoFibreProductOver.fst_comp_eq
  letI : (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).GuitartExact :=
    TwoFibreProductOver.guitartExact_twoFibreProductSquare p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  letI : (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).op.GuitartExact := inferInstance
  @asIso _ _ _ _ (Stacks.SheafOfModules.directImageBaseChange (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g)
    (ringStructureSheafCore_obj_eq B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
    (ringStructureSheafCore_obj_eq B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ)
    (ringStructureSheafCore_obj_eq B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ)
    (ringStructureSheafCore_obj_eq B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq τ hτ)
    (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
    (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ)
    (moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, max (u + 1) a} B S hS
      p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
    (moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, max (u + 1) a} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ)
    (moduleSheafPushforward_leg_smul B S hS p𝒳 p𝒴 f τ hτ h𝒳 h𝒴 hfc)
    (moduleSheafPushforward_leg_smul B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g)
      p𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ hτ
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      TwoFibreProductOver.snd_comp_eq)
    (structureSheaf_baseChange_scalar B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc))
    (Stacks.SheafOfModules.isIso_directImageBaseChange (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g)
    (ringStructureSheafCore_obj_eq B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
    (ringStructureSheafCore_obj_eq B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ)
    (ringStructureSheafCore_obj_eq B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ)
    (ringStructureSheafCore_obj_eq B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq τ hτ)
    (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
    (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ)
    (moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, max (u + 1) a} B S hS
      p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
    (moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u, max (u + 1) a} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ)
    (moduleSheafPushforward_leg_smul B S hS p𝒳 p𝒴 f τ hτ h𝒳 h𝒴 hfc)
    (moduleSheafPushforward_leg_smul B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g)
      p𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ hτ
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      TwoFibreProductOver.snd_comp_eq)
    (structureSheaf_baseChange_scalar B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc))

end ModuleLinear

section ModuleAcyclic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴' : Type (u + 1)} [Category.{u} 𝒴']
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- Sheaves of modules over the structure sheaf of a category over the big fppf category of `S`
have enough injectives. -/
instance enoughInjectives_sheafOfModules_ringStructureSheafCore {𝒵 : Type (u + 1)}
    [Category.{u} 𝒵] (p : 𝒵 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) :
    EnoughInjectives (SheafOfModules.{max (u + 1) a} (ringStructureSheafCore B S hS p hp τ hτ)) :=
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, a} _

/-- Stacks 06X2 for the inverse image of sheaves of modules of Stacks 06WE: along a faithful
1-morphism whose source has equalizers it preserves injectives. -/
theorem injective_modulePullback_obj {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    {ℬ : Type (u + 1)} [Category.{u} ℬ]
    (pA : 𝒜 ⥤ BigFppfOver B S hS) (pB : ℬ ⥤ BigFppfOver B S hS)
    (hA : pA.IsFiberedInGroupoids) (hB : pB.IsFiberedInGroupoids) (F : 𝒜 ⥤ ℬ) (hF : F ⋙ pB = pA)
    [F.Faithful] [HasEqualizers 𝒜]
    (I : SheafOfModules.{max (u + 1) a} (ringStructureSheafCore B S hS pB hB τ hτ)) [Injective I] :
    Injective ((modulePullback.{u, _, _, max (u + 1) a} B S hS pA pB hA hB F hF τ hτ).obj I) := by
  have h := injective_sheafOfModules_pushforward_obj_of_injective.{u, u + 1, u + 1, u, u,
    max (u + 1) a} B S hS pA pB F τ hA hB hF hτ I
  cases hF
  exact h

/-- The inverse image of an injective sheaf of modules along two composable 1-morphisms, taken
in two steps, is injective when the composite is faithful and its source has equalizers
(Stacks 06X2). -/
theorem injective_modulePullback_modulePullback {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    {ℬ : Type (u + 1)} [Category.{u} ℬ] {𝒞 : Type (u + 1)} [Category.{u} 𝒞]
    (pA : 𝒜 ⥤ BigFppfOver B S hS) (pB : ℬ ⥤ BigFppfOver B S hS)
    (pC : 𝒞 ⥤ BigFppfOver B S hS) (hA : pA.IsFiberedInGroupoids) (hB : pB.IsFiberedInGroupoids)
    (hC : pC.IsFiberedInGroupoids) (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) (hF : F ⋙ pB = pA)
    (hG : G ⋙ pC = pB) [(F ⋙ G).Faithful] [HasEqualizers 𝒜]
    (I : SheafOfModules.{max (u + 1) a} (ringStructureSheafCore B S hS pC hC τ hτ)) [Injective I] :
    Injective ((modulePullback.{u, _, _, max (u + 1) a} B S hS pA pB hA hB F hF τ hτ).obj
      ((modulePullback.{u, _, _, max (u + 1) a} B S hS pB pC hB hC G hG τ hτ).obj I)) := by
  have hFG : (F ⋙ G) ⋙ pC = pA := by rw [Functor.assoc, hG, hF]
  have h := injective_sheafOfModules_pushforward_obj_of_injective.{u, u + 1, u + 1, u, u,
    max (u + 1) a} B S hS pA pC (F ⋙ G) τ hA hC hFG hτ I
  cases hF
  cases hG
  exact h

attribute [local instance] wEqualsLocallyBijective_associatedTopology_of_essentiallySmall

/-- The inverse image of sheaves of modules of Stacks 06WE between categories fibred in groupoids
is additive: on underlying presheaves it is precomposition followed by a transport of scalars.
Used below as a local instance. -/
theorem additive_modulePullback_ofFiberedInGroupoids {𝒜 : Type*} [Category* 𝒜] {ℬ : Type*}
    [Category* ℬ]
    (pA : 𝒜 ⥤ BigFppfOver B S hS) (pB : ℬ ⥤ BigFppfOver B S hS)
    (hA : pA.IsFiberedInGroupoids) (hB : pB.IsFiberedInGroupoids) (F : 𝒜 ⥤ ℬ) (hF : F ⋙ pB = pA) :
    (modulePullback.{u, _, _, a} B S hS pA pB hA hB F hF τ hτ).Additive where
  map_add := by intros; rfl

attribute [local instance] additive_modulePullback_ofFiberedInGroupoids


/-- **The inverse image `(g')^*` carries injective sheaves of modules to `f'_*`-acyclic ones.**
This is `isZero_rightDerived_sheafPushforwardCocontinuous_snd_obj` for sheaves of modules: the
underlying abelian sheaf of `Rⁿf'_*((g')^*I)` is the sheafification of the derived presheaf of
sections over the fibres, and restriction of sheaves of modules to the fibres is exact and
preserves injectives (Stacks 06X2). -/
theorem isZero_rightDerived_moduleSheafPushforward_snd_obj
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [HasEqualizers (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)]
    (I : SheafOfModules.{max (u + 1) a} (ringStructureSheafCore B S hS p𝒳 h𝒳 τ hτ)) [Injective I]
    (n : ℕ) (hn : 0 < n) :
    letI := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ
        hτ).right_adjoint_additive
    IsZero (((moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ
        hτ).rightDerived n).obj
      ((modulePullback B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq τ hτ).obj I)) := by
  let pX' := TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g
  let hX' : pX'.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let g' := TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g
  let f' := TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g
  let A := AddCommGrpCat.{max (u + 1) a}
  let OX' := ringStructureSheafCore B S hS pX' hX' τ hτ
  let OY' := ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ
  let JY' := associatedTopology B S hS p𝒴' τ
  let P' := moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS pX' p𝒴' hX' h𝒴' f'
    TwoFibreProductOver.snd_comp_eq τ hτ
  let := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS pX' p𝒴' hX' h𝒴'
    f' TwoFibreProductOver.snd_comp_eq τ hτ).right_adjoint_additive
  let J := (modulePullback B S hS pX' p𝒳 hX' h𝒳 g' TwoFibreProductOver.fst_comp_eq τ hτ).obj I
  let T := SheafOfModules.toSheaf.{max (u + 1) a} OY'
  let : PreservesFiniteColimits T := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits OY'
  let : T.PreservesHomology := inferInstance
  let : p𝒴'.IsFibered := h𝒴'.isFibered
  let : pX'.IsFibered := hX'.isFibered
  let := isCocontinuous_of_isFiberedInGroupoids B S hS pX' p𝒴' f' τ h𝒴'
    TwoFibreProductOver.snd_comp_eq
  -- reduce to the underlying abelian sheaf
  refine (IsZero.iff_id_eq_zero _).2 (T.map_injective ?_)
  rw [T.map_id, T.map_zero]
  refine IsZero.eq_of_src ?_ _ _
  refine IsZero.of_iso ?_ ((Functor.rightDerivedCompIso P' T n).app J).symm
  -- the direct image followed by `toSheaf` is the sheafified right Kan extension
  let G' := (SheafOfModules.forget OX' ⋙ PresheafOfModules.toPresheaf OX'.obj) ⋙ f'.op.ran
  let : G'.Additive := by
    let := (f'.op.ranAdjunction A).right_adjoint_additive
    infer_instance
  let Sh := presheafToSheaf JY' A
  let : Sh.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels Sh
  have e : P' ⋙ T ≅ G' ⋙ Sh :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (P' ⋙ T) (sheafificationNatIso JY' A) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (moduleSheafPushforwardCompToPresheafIso.{u, u + 1, u, u + 1, u,
        max (u + 1) a} B S hS pX' p𝒴' hX' h𝒴' f' TwoFibreProductOver.snd_comp_eq τ hτ) Sh
  refine IsZero.of_iso ?_ ((Functor.rightDerivedIsoOfNatIso e n).app J)
  refine IsZero.of_iso ?_ ((Functor.rightDerivedCompIso G' Sh n).app J)
  refine Functor.map_isZero Sh (X := (G'.rightDerived n).obj J) (Functor.isZero _ fun y => ?_)
  obtain ⟨y'⟩ := y
  let π := CostructuredArrow.proj f' y'
  let pE := π ⋙ pX'
  have hE : pE.IsFiberedInGroupoids :=
    (Functor.IsFiberedInGroupoids.costructuredArrow_proj f' y').comp _ _ hX'
  let OE := ringStructureSheafCore B S hS pE hE τ hτ
  let : (π ⋙ g').Faithful :=
    TwoFibreProductOver.faithful_costructuredArrowProj_comp_fst p𝒳 p𝒴' p𝒴 f g h𝒴' y'
  let P := modulePullback.{u, _, _, max (u + 1) a} B S hS pE pX' hE hX' π rfl τ hτ
  let : PreservesFiniteLimits P :=
    preservesFiniteLimits_modulePullback'.{u, u + 1, u, u + 1, u, max (u + 1) a}
      B S hS pE pX' hE hX' π rfl τ hτ
  let := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS pE pX' hE hX' π
    rfl τ hτ).leftAdjoint_preservesColimits
  let : P.PreservesHomology := inferInstance
  let : P.PreservesInjectiveObjects := ⟨fun {K} hK => by
    let := hK
    exact injective_modulePullback_obj B S hS τ hτ pE pX' hE hX' π rfl K⟩
  have hinj : Injective (P.obj J) :=
    injective_modulePullback_modulePullback B S hS τ hτ pE pX' p𝒳 hE hX' h𝒳 π g' rfl
      TwoFibreProductOver.fst_comp_eq I
  exact isZero_rightDerived_ran_obj_of_injective f' y'
    (SheafOfModules.forget OX' ⋙ PresheafOfModules.toPresheaf OX'.obj)
    (SheafOfModules.forget OE ⋙ PresheafOfModules.toPresheaf OE.obj) P
    (modulePullbackCompToPresheafIso.{u, u + 1, u, u + 1, u, a} B S hS pE pX' hE hX' π rfl τ hτ)
    J n hn

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The direct image of sheaves of modules of Stacks 06WE is additive, being a right adjoint. -/
theorem additive_moduleSheafPushforward_univ {𝒜 : Type (u + 1)} [Category.{u} 𝒜]
    {ℬ : Type (u + 1)} [Category.{u} ℬ]
    (pA : 𝒜 ⥤ BigFppfOver B S hS) (pB : ℬ ⥤ BigFppfOver B S hS)
    (hA : pA.IsFiberedInGroupoids) (hB : pB.IsFiberedInGroupoids) (F : 𝒜 ⥤ ℬ) (hF : F ⋙ pB = pA) :
    (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS pA pB hA hB F hF τ hτ).Additive :=
  (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS pA pB hA hB F hF τ
    hτ).right_adjoint_additive

attribute [local instance] additive_moduleSheafPushforward_univ

/-- **Base change for higher direct images of sheaves of modules.** For the canonical
2-cartesian square of categories fibred in groupoids over the big fppf category of `S` whose apex
has equalizers, and any topology `τ` coarser than the fppf topology,
`Rⁿf_* ⋙ g^* ≅ (g')^* ⋙ Rⁿf'_*` on sheaves of modules, for every `n`. -/
noncomputable def moduleHigherDirectImageBaseChangeIsoOfHasEqualizers
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [HasEqualizers (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)] (n : ℕ) :
    (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ
          hτ).rightDerived n ⋙
        modulePullback B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ ≅
      modulePullback B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq τ hτ ⋙
        (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
          (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ
            hτ).rightDerived n := by
  let pX' := TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g
  let hX' : pX'.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let g' := TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g
  let f' := TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g
  let Pf := moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ
  let Pf' := moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS pX' p𝒴' hX' h𝒴' f'
    TwoFibreProductOver.snd_comp_eq τ hτ
  let Qg := modulePullback.{u, _, _, max (u + 1) a} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ
  let Qg' := modulePullback.{u, _, _, max (u + 1) a} B S hS pX' p𝒳 hX' h𝒳 g'
    TwoFibreProductOver.fst_comp_eq τ hτ
  let : PreservesFiniteLimits Qg :=
    preservesFiniteLimits_modulePullback'.{u, u + 1, u, u + 1, u, max (u + 1) a}
      B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ
  let := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g
    hgc τ hτ).leftAdjoint_preservesColimits
  let : Qg.PreservesHomology := inferInstance
  let : PreservesFiniteLimits Qg' :=
    preservesFiniteLimits_modulePullback'.{u, u + 1, u, u + 1, u, max (u + 1) a}
      B S hS pX' p𝒳 hX' h𝒳 g' TwoFibreProductOver.fst_comp_eq τ hτ
  let := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS pX' p𝒳 hX' h𝒳 g'
    TwoFibreProductOver.fst_comp_eq τ hτ).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits Qg' := inferInstance
  let := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS pX' p𝒴' hX' h𝒴'
    f' TwoFibreProductOver.snd_comp_eq τ hτ).rightAdjoint_preservesLimits
  let : PreservesFiniteLimits Pf' := inferInstance
  -- Acyclicity is phrased through derived categories; any models serve, and these are local.
  letI := HasDerivedCategory.standard
    (SheafOfModules (ringStructureSheafCore B S hS pX' hX' τ hτ))
  letI := HasDerivedCategory.standard
    (SheafOfModules (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ))
  have hac : ∀ I, Injective I → Pf'.rightAcyclic (Qg'.obj I) := fun I hI => by
    let := hI
    refine (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic Pf' (Qg'.obj I)).2 fun m hm => ?_
    exact isZero_rightDerived_moduleSheafPushforward_snd_obj B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴'
      h𝒴 hfc hgc I m hm
  exact (Functor.rightDerivedCompIso Pf Qg n).symm ≪≫
    Functor.rightDerivedIsoOfNatIso
      (moduleSheafPushforwardBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc) n ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic Qg' Pf' hac n

end ModuleAcyclic

namespace AlgebraicStacks

universe w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The 2-fibre product of algebraic stacks has equalizers: it is an algebraic stack
(Stacks 04T2), and algebraic stacks have equalizers (Stacks 06WY). -/
theorem hasEqualizers_twoFibreProductOver {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    HasEqualizers (TwoFibreProductOver 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)) :=
  AlgebraicStacks.hasEqualizers B S hS (twoFibreProductAlgebraicStack B S hS f g)

/-- **Stacks 075H for abelian sheaves.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴` be 1-morphisms of
algebraic stacks over `S`, with 2-cartesian square
```
𝒴' ×_𝒴 𝒳 --- g' ---> 𝒳
   |                 |
   f'                f
   v                 v
  𝒴' ------ g -----> 𝒴
```
For every topology `τ` on the schemes of the big fppf site, the base change map is an
isomorphism `g⁻¹Rⁱf_*ℱ ≅ Rⁱf'_*((g')⁻¹ℱ)` of abelian sheaves on `𝒴'_τ`, functorially in the
abelian sheaf `ℱ` on `𝒳_τ`, for every `i`. -/
@[stacks 075H "abelian sheaves: g⁻¹Rⁱf_*F ≅ Rⁱf'_*((g')⁻¹F) for every i, naturally in F"]
noncomputable def abelianHigherDirectImageBaseChangeIso {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (τ : GrothendieckTopology B.Schemes) (n : ℕ) :
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor g.hom)).IsFibered :=
      isFibered_twoFibreProductStructureFunctor _ _ _ _ _ 𝒳.val.property 𝒴'.val.property
        𝒴.val.property (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    letI : 𝒳.val.val.p.IsFibered := 𝒳.val.property.isFibered
    letI : 𝒴'.val.val.p.IsFibered := 𝒴'.val.property.isFibered
    letI : 𝒴.val.val.p.IsFibered := 𝒴.val.property.isFibered
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS _ _
      (CatFiberedInGroupoids.homFunctor f.hom) τ 𝒴.val.property
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    letI := isContinuous_of_isFiberedInGroupoids B S hS _ _
      (CatFiberedInGroupoids.homFunctor g.hom) τ 𝒴.val.property
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    letI := isContinuous_of_isFiberedInGroupoids B S hS _ _
      (TwoFibreProductOver.fst 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
      τ 𝒳.val.property TwoFibreProductOver.fst_comp_eq
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS _ _
      (TwoFibreProductOver.snd 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
      τ 𝒴'.val.property TwoFibreProductOver.snd_comp_eq
    letI : ((CatFiberedInGroupoids.homFunctor f.hom).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS 𝒳.val.val.p τ)
        (associatedTopology B S hS 𝒴.val.val.p τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS _ _ _ τ
        (𝒴.val.property.isFibredOneMorphism (CatFiberedInGroupoids.homFunctor_comp_p f.hom))
    letI : ((TwoFibreProductOver.snd 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor g.hom)).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS (TwoFibreProductOver.structureFunctor 𝒳.val.val.p
          𝒴'.val.val.p 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor g.hom)) τ)
        (associatedTopology B S hS 𝒴'.val.val.p τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS _ _ _ τ
        (𝒴'.val.property.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq)
    ((CatFiberedInGroupoids.homFunctor f.hom).sheafPushforwardCocontinuous
          AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS 𝒳.val.val.p τ)
          (associatedTopology B S hS 𝒴.val.val.p τ)).rightDerived n ⋙
        (CatFiberedInGroupoids.homFunctor g.hom).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS 𝒴'.val.val.p τ)
          (associatedTopology B S hS 𝒴.val.val.p τ) ≅
      (TwoFibreProductOver.fst 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor g.hom)).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS (TwoFibreProductOver.structureFunctor 𝒳.val.val.p
            𝒴'.val.val.p 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
            (CatFiberedInGroupoids.homFunctor g.hom)) τ)
          (associatedTopology B S hS 𝒳.val.val.p τ) ⋙
        ((TwoFibreProductOver.snd 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom)
            (CatFiberedInGroupoids.homFunctor g.hom)).sheafPushforwardCocontinuous
            AddCommGrpCat.{max (u + 1) a}
            (associatedTopology B S hS (TwoFibreProductOver.structureFunctor 𝒳.val.val.p
              𝒴'.val.val.p 𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
              (CatFiberedInGroupoids.homFunctor g.hom)) τ)
            (associatedTopology B S hS 𝒴'.val.val.p τ)).rightDerived n :=
  letI := hasEqualizers_twoFibreProductOver B S hS f g
  abelianHigherDirectImageBaseChangeIsoOfHasEqualizers B S hS _ _ _ _ _ τ 𝒳.val.property
    𝒴'.val.property 𝒴.val.property (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom) n

attribute [local instance] additive_moduleSheafPushforward_univ

/-- **Stacks 075H for sheaves of modules.** For 1-morphisms `f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴` of
algebraic stacks over `S` with 2-cartesian square `𝒴' ×_𝒴 𝒳` as in
`AlgebraicStacks.abelianHigherDirectImageBaseChangeIso`, and every topology `τ` coarser than the
fppf topology, the base change map is an isomorphism `g^*Rⁱf_*ℱ ≅ Rⁱf'_*((g')^*ℱ)` of sheaves of
`𝒪_{𝒴'}`-modules, functorially in the sheaf of `𝒪_𝒳`-modules `ℱ`, for every `i`; the higher
direct images are the right derived functors on sheaves of modules. -/
@[stacks 075H "sheaves of modules: g⁻¹Rⁱf_*F ≅ Rⁱf'_*((g')⁻¹F) in Mod(O) for every i, \
naturally in F"]
noncomputable def moduleHigherDirectImageBaseChangeIso {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (n : ℕ) :
    (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.property 𝒴.val.property (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) τ hτ).rightDerived n ⋙
        modulePullback B S hS 𝒴'.val.val.p 𝒴.val.val.p 𝒴'.val.property 𝒴.val.property
          (CatFiberedInGroupoids.homFunctor g.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p g.hom) τ hτ ≅
      modulePullback B S hS (TwoFibreProductOver.structureFunctor 𝒳.val.val.p 𝒴'.val.val.p
          𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor g.hom)) 𝒳.val.val.p
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ 𝒳.val.property 𝒴'.val.property
            𝒴.val.property (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
            (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) 𝒳.val.property
          (TwoFibreProductOver.fst 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
          TwoFibreProductOver.fst_comp_eq τ hτ ⋙
        (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
          (TwoFibreProductOver.structureFunctor 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
          𝒴'.val.val.p
          (TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _ 𝒳.val.property 𝒴'.val.property
            𝒴.val.property (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
            (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) 𝒴'.val.property
          (TwoFibreProductOver.snd 𝒳.val.val.p 𝒴'.val.val.p 𝒴.val.val.p
            (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom))
          TwoFibreProductOver.snd_comp_eq τ hτ).rightDerived n :=
  letI := hasEqualizers_twoFibreProductOver B S hS f g
  moduleHigherDirectImageBaseChangeIsoOfHasEqualizers B S hS _ _ _ _ _ τ hτ 𝒳.val.property
    𝒴'.val.property 𝒴.val.property (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom) n

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
