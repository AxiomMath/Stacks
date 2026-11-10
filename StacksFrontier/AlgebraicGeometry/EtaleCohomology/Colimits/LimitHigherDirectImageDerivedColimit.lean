module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.ComplexHigherDirectImageColimitTheorem

/-!
# Higher direct images of a pulled back bounded below object along a limit of morphisms

Let `I` be a directed set, let `g_i : X_i ⟶ S_i` be an inverse system of quasi-compact and
quasi-separated morphisms of schemes over `I` with affine transition morphisms `f_{i'i}`,
`h_{i'i}`, and let `g : X ⟶ S` be its limit, with projections `f_i : X ⟶ X_i`, `h_i : S ⟶ S_i`.
Let `0 ∈ I` and `K_0 ∈ D^+(X_{0, étale})`, let `K_i` be the pullback of `K_0` to `X_i` for
`i ≥ 0` and `K` the pullback of `K_0` to `X`. Then

`R^pg_*K = colim_{i ≥ 0} h_i^{-1}R^pg_{i, *}K_i` for all `p ∈ ℤ` ([Stacks, Tag 0GIU]).

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.aboveInclusion`: the inclusion of the indices
  `i ≥ 0` into `I`, on opposite categories; it is initial.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.derivedLevelPullbackComparison`,
  `Stacks.EtaleCohomology.LimitHigherDirectImage.derivedLimitPullbackComparison`: the
  comparisons `R f_{i'i}^{-1}K_i ≅ K_{i'}` and `R f_i^{-1}K_i ≅ K` of derived inverse images
  along the composites `f_{i'0} = f_{i'i} ≫ f_{i0}` and `f_0 = f_i ≫ f_{i0}`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.derivedPullbackHigherDirectImageColimit`:
  [Stacks, Tag 0GIU].

## Implementation notes

The source proves 0GIU by induction on the cohomological amplitude, using the truncation
triangles `H^a(K_0)[-a] → K_0 → τ_{≥ a+1}K_0`. Here it is deduced from
`Stacks.EtaleCohomology.LimitHigherDirectImage.complexHigherDirectImageColimit`
(Stacks 0GIV) instead: `K_0` is represented by a complex `𝒢^•` vanishing in degrees `< a`, the
pullbacks of `𝒢^•` to the `X_i`, `i ≥ 0`, form a uniformly bounded below system of complexes whose
colimit is the pullback of `𝒢^•` to `X`, and the comparisons of derived inverse images identify
the colimit assertion of 0GIV for that system with the one of 0GIU. The transition maps of 0GIU
are the derived base change maps of the transition squares composed with `R^pg_{i', *}` of the
comparisons `R f_{i'i}^{-1}K_i ≅ K_{i'}`, and its cocone maps those of the projection squares
composed with `R^pg_*` of `R f_i^{-1}K_i ≅ K`.

The index category of the colimit is the set `{i ∈ I | i ≥ 0}`, as in the source; the inverse
systems are restricted to it along `aboveInclusion`, and their limits are unchanged because the
inclusion is initial.

## References

* [Stacks Project, Tag 0GIU](https://stacks.math.columbia.edu/tag/0GIU)
* [Stacks Project, Tag 0GIV](https://stacks.math.columbia.edu/tag/0GIV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex (plusDerivedObj)

universe u

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard

/-! ### The indices above a given one -/

section Above

variable {I : Type u} [Preorder I] (i₀ : I)

/-- The indices above a directed set's element form a directed set. -/
theorem isDirected_Ici [IsDirected I (· ≤ ·)] : IsDirected (Set.Ici i₀) (· ≤ ·) :=
  ⟨fun a b => by
    obtain ⟨c, ha, hb⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans ha⟩, ha, hb⟩⟩

attribute [local instance] isDirected_Ici

/-- **The inclusion of the indices `i ≥ i₀`**, on opposite categories. -/
abbrev aboveInclusion : (Set.Ici i₀)ᵒᵖ ⥤ Iᵒᵖ :=
  (Subtype.mono_coe (fun i => i ∈ Set.Ici i₀)).functor.op

/-- The inclusion of the indices `i ≥ i₀` is full. -/
instance : (aboveInclusion i₀).Full where
  map_surjective {j j'} f := ⟨(homOfLE (show j'.unop ≤ j.unop from leOfHom f.unop)).op, rfl⟩

/-- The inclusion of the indices `i ≥ i₀` is faithful. -/
instance : (aboveInclusion i₀).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- **The inclusion of the indices `i ≥ i₀` is initial**, `I` being directed: a limit over `I` is
a limit over the indices `i ≥ i₀`. -/
instance [IsDirected I (· ≤ ·)] [Nonempty I] : (aboveInclusion i₀).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun d => by
    obtain ⟨c, hc₀, hc⟩ := directed_of (· ≤ ·) i₀ d.unop
    exact ⟨op ⟨c, hc₀⟩, ⟨(homOfLE hc).op⟩⟩

/-- The transition `i ⟶ i₀` of `Iᵒᵖ` for an index `i ≥ i₀`. -/
abbrev aboveTransition (j : (Set.Ici i₀)ᵒᵖ) : (aboveInclusion i₀).obj j ⟶ op i₀ :=
  (homOfLE j.unop.2).op

end Above

/-! ### Comparisons of derived inverse images -/

section Comparison

/-- The comparison of derived inverse images of `K_0` along a factorisation `f = f₂ ≫ f₁`. -/
abbrev derivedPullbackComparison {X₀ X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ X₀) (f₂ : X₂ ⟶ X₁)
    (f : X₂ ⟶ X₀) (hf : f = f₂ ≫ f₁) (K₀ : PlusAb X₀) :
    (derivedPullbackAb f₂).obj ((derivedPullbackAb f₁).obj K₀) ⟶ (derivedPullbackAb f).obj K₀ :=
  (smallEtaleDerivedPullbackAbPlusComp' f₁ f₂ f hf).hom.app K₀

/-- The comparison `smallEtaleComplexPullbackComparison` of the inverse image of a complex with
itself is an isomorphism. -/
instance isIso_smallEtaleComplexPullbackComparison_id (a : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ) [G.IsStrictlyGE a]
    [CochainComplex.IsStrictlyGE
      (((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) a] :
    IsIso (smallEtaleComplexPullbackComparison a f G _ (𝟙 _)) := by
  let : IsIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnith :=
    (smallEtalePullbackAb f).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have : IsIso (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map
      (𝟙 (((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G))) :
        (smallEtalePullbackAb f).mapHomotopyCategoryPlus.obj (CochainComplex.plusHomotopyObj a G) ⟶
          CochainComplex.plusHomotopyObj a
            (((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)) :=
    (ObjectProperty.isoMk _ ((HomotopyCategory.quotient _ _).mapIso (Iso.refl _)) :
      (smallEtalePullbackAb f).mapHomotopyCategoryPlus.obj (CochainComplex.plusHomotopyObj a G) ≅
        CochainComplex.plusHomotopyObj a
          (((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)).isIso_hom
  rw [smallEtaleComplexPullbackComparison_eq]
  infer_instance

/-- **The identification of the class of the inverse image of a complex with the derived inverse
image of `K_0`**, for a complex `𝒢^•` and an isomorphism `e : K_0 ≅ 𝒢^•` in `D^+`. -/
def complexPullbackIso (a : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ) [G.IsStrictlyGE a]
    [CochainComplex.IsStrictlyGE
      (((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) a]
    {K₀ : PlusAb Y} (e : K₀ ≅ plusDerivedObj a G) :
    plusDerivedObj a (((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) ≅
      (derivedPullbackAb f).obj K₀ :=
  (asIso (smallEtaleComplexPullbackComparison a f G _ (𝟙 _))).symm ≪≫
    (derivedPullbackAb f).mapIso e.symm

/-- **The identifications of inverse images of a complex with derived inverse images are
compatible with composition.** For `f = f₂ ≫ f₁`, the identification for `f₁`, pulled back along
`f₂` and followed by the comparison of derived inverse images, is the comparison
`smallEtaleComplexPullbackComparison` of the identification of inverse images of complexes along
the factorisation, followed by the identification for `f`. -/
theorem complexPullbackIso_comp (a : ℤ) {X₀ X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ X₀) (f₂ : X₂ ⟶ X₁)
    (f : X₂ ⟶ X₀) (hf : f = f₂ ≫ f₁)
    (G : CochainComplex (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) ℤ) [G.IsStrictlyGE a]
    [CochainComplex.IsStrictlyGE
      (((smallEtalePullbackAb f₁).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) a]
    [CochainComplex.IsStrictlyGE
      (((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G) a]
    {K₀ : PlusAb X₀} (e : K₀ ≅ plusDerivedObj a G) :
    (derivedPullbackAb f₂).map (complexPullbackIso a f₁ G e).hom ≫
        derivedPullbackComparison f₁ f₂ f hf K₀ =
      smallEtaleComplexPullbackComparison a f₂ _ _
          ((NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' f₂ f₁ f hf)
            (ComplexShape.up ℤ)).hom.app G) ≫
        (complexPullbackIso a f G e).hom := by
  have hp := smallEtaleComplexPullbackComparison_paste a f₁ f₂ f hf G _ _ (𝟙 _)
    ((NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' f₂ f₁ f hf)
      (ComplexShape.up ℤ)).hom.app G) (𝟙 _)
    (by
      simp only [CategoryTheory.Functor.map_id]
      exact (NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' f₂ f₁ f hf)
        (ComplexShape.up ℤ)).inv_hom_id_app G)
  have hn := (smallEtaleDerivedPullbackAbPlusComp' f₁ f₂ f hf).hom.naturality e.inv
  simp only [Functor.comp_map] at hn
  have key : smallEtaleComplexPullbackComparison a f₂ _ _
        ((NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' f₂ f₁ f hf)
          (ComplexShape.up ℤ)).hom.app G) =
      ((derivedPullbackAb f₂).map (inv (smallEtaleComplexPullbackComparison a f₁ G _ (𝟙 _))) ≫
        (smallEtaleDerivedPullbackAbPlusComp' f₁ f₂ f hf).hom.app (plusDerivedObj a G)) ≫
          smallEtaleComplexPullbackComparison a f G _ (𝟙 _) := by
    rw [hp]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_inv, IsIso.inv_hom_id_assoc]
  rw [key]
  simp only [complexPullbackIso, derivedPullbackComparison, Iso.trans_hom, Iso.symm_hom,
    asIso_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [hn]

/-- A bounded below derived object is the class of a complex vanishing below some degree. -/
theorem exists_iso_plusDerivedObj {X : Scheme.{u}} (K : PlusAb X) :
    ∃ (a : ℤ) (G : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ)
      (_ : G.IsStrictlyGE a), Nonempty (K ≅ plusDerivedObj a G) := by
  obtain ⟨a, ha⟩ := K.property
  have : K.obj.IsGE a := ha
  obtain ⟨G, _, ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K.obj a
  exact ⟨a, G, inferInstance, ⟨DerivedCategory.Plus.ι.preimageIso
    (eK ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app G)⟩⟩

/-! ### Transport of a colimit of a system along isomorphisms -/

section Transport

variable {𝒞 : Type*} [Category* 𝒞] {K : Type*} [Quiver K] {A A' : K → 𝒞}
  {T : ∀ {i j : K}, (i ⟶ j) → (A j ⟶ A i)} {T' : ∀ {i j : K}, (i ⟶ j) → (A' j ⟶ A' i)}
  {B B' : 𝒞} {ψ : ∀ i, A i ⟶ B} {ψ' : ∀ i, A' i ⟶ B'} (θ : ∀ i, A i ≅ A' i) (e : B ≅ B')
  (hT : ∀ {i j : K} (a : i ⟶ j), T a ≫ (θ i).hom = (θ j).hom ≫ T' a)
  (hψ : ∀ i, ψ i ≫ e.hom = (θ i).hom ≫ ψ' i)

omit [Quiver K] in
/-- Maps transported along isomorphisms compose as the original ones do. -/
theorem comp_eq_of_iso {X₀ X₁ X₂ Y₀ Y₁ Y₂ : 𝒞} (θ₀ : X₀ ≅ Y₀) (θ₁ : X₁ ≅ Y₁) (θ₂ : X₂ ≅ Y₂)
    {t₀₁ : X₁ ⟶ X₀} {t₁₂ : X₂ ⟶ X₁} {t₀₂ : X₂ ⟶ X₀} {s₀₁ : Y₁ ⟶ Y₀} {s₁₂ : Y₂ ⟶ Y₁}
    {s₀₂ : Y₂ ⟶ Y₀} (h₀₁ : t₀₁ ≫ θ₀.hom = θ₁.hom ≫ s₀₁) (h₁₂ : t₁₂ ≫ θ₁.hom = θ₂.hom ≫ s₁₂)
    (h₀₂ : t₀₂ ≫ θ₀.hom = θ₂.hom ≫ s₀₂) (hc : t₀₂ = t₁₂ ≫ t₀₁) : s₀₂ = s₁₂ ≫ s₀₁ := by
  rw [← cancel_epi θ₂.hom, ← h₀₂, hc, Category.assoc, h₀₁, reassoc_of% h₁₂]

include hT hψ in
/-- The cocone maps of a system transported along isomorphisms form a cocone as the original
ones do. -/
theorem cocone_of_isoSystem (hc : ∀ {i j : K} (a : i ⟶ j), T a ≫ ψ i = ψ j) {i j : K}
    (a : i ⟶ j) : T' a ≫ ψ' i = ψ' j := by
  have hT' : T' a = (θ j).inv ≫ T a ≫ (θ i).hom := by rw [hT a, Iso.inv_hom_id_assoc]
  have hψ' : ∀ i, ψ' i = (θ i).inv ≫ ψ i ≫ e.hom := fun i => by rw [hψ i, Iso.inv_hom_id_assoc]
  rw [hT', hψ', hψ']
  simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% (hc a)]

end Transport

end Comparison


/-! ### Stacks 0GIU -/

section Main

attribute [local instance] isDirected_Ici

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
  (γ : DX ⟶ DS) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] {cX : Cone DX} {cS : Cone DS} (hcX : IsLimit cX)
  (hcS : IsLimit cS) (i₀ : I)

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)] in
/-- The transitions to `i₀` compose with the transition maps of the indices above `i₀`. -/
theorem map_aboveTransition {j j' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j') :
    DX.map (aboveTransition i₀ j) = DX.map ((aboveInclusion i₀).map c) ≫
      DX.map (aboveTransition i₀ j') := by
  rw [← DX.map_comp]
  rfl

/-- The pullback `K_i` to `X_i`, `i ≥ i₀`, of `K_0 ∈ D^+(X_{i₀, étale})`. -/
abbrev aboveLevelPullback (K₀ : PlusAb (DX.obj (op i₀))) (j : (Set.Ici i₀)ᵒᵖ) :
    PlusAb (DX.obj ((aboveInclusion i₀).obj j)) :=
  (derivedPullbackAb (DX.map (aboveTransition i₀ j))).obj K₀

/-- **The comparison `R f_{i'i}^{-1}K_i ≅ K_{i'}`** of derived inverse images along
`f_{i'0} = f_{i'i} ≫ f_{i0}`. -/
abbrev derivedLevelPullbackComparison (K₀ : PlusAb (DX.obj (op i₀))) {j j' : (Set.Ici i₀)ᵒᵖ}
    (c : j ⟶ j') :
    (derivedPullbackAb (DX.map ((aboveInclusion i₀).map c))).obj (aboveLevelPullback i₀ K₀ j') ⟶
      aboveLevelPullback i₀ K₀ j :=
  derivedPullbackComparison (DX.map (aboveTransition i₀ j')) (DX.map ((aboveInclusion i₀).map c))
    (DX.map (aboveTransition i₀ j)) (map_aboveTransition i₀ c) K₀

/-- **The comparison `R f_i^{-1}K_i ≅ K`** of derived inverse images along
`f_0 = f_i ≫ f_{i0}`. -/
abbrev derivedLimitPullbackComparison (K₀ : PlusAb (DX.obj (op i₀))) (j : (Set.Ici i₀)ᵒᵖ) :
    (derivedPullbackAb (cX.π.app ((aboveInclusion i₀).obj j))).obj (aboveLevelPullback i₀ K₀ j) ⟶
      (derivedPullbackAb (cX.π.app (op i₀))).obj K₀ :=
  derivedPullbackComparison (DX.map (aboveTransition i₀ j)) (cX.π.app ((aboveInclusion i₀).obj j))
    (cX.π.app (op i₀)) (cX.w (aboveTransition i₀ j)).symm K₀

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] in
/-- The derived comparison map of a projection square does not depend on how the limit morphism
is presented. -/
theorem derivedBaseChangeHomologyMap_congr_limit {X' Y S T : Scheme.{u}} (f' : X' ⟶ S)
    (g : T ⟶ S) {h h' : Y ⟶ X'} (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) (w' : h' ≫ f' = e ≫ g)
    (hh : h' = h) (p : ℤ) (L : PlusAb T) (M : PlusAb Y)
    (κ : (derivedPullbackAb e).obj L ⟶ M) :
    derivedBaseChangeHomologyMap f' g h' e w' p L M κ ≫
        eqToHom (congrArg (fun z => (homologyAb X' p).obj ((derivedPushforwardAb z).obj M)) hh) =
      derivedBaseChangeHomologyMap f' g h e w p L M κ := by
  subst hh
  obtain rfl : w' = w := rfl
  exact Category.comp_id _

/-- The inverse system `(X_i)_{i ≥ i₀}`, `(S_i)_{i ≥ i₀}` and the morphism `g_i` between them,
restricted to the indices above `i₀`. -/
abbrev aboveMorphism : aboveInclusion i₀ ⋙ DX ⟶ aboveInclusion i₀ ⋙ DS :=
  Functor.whiskerLeft (aboveInclusion i₀) γ

/-- **The system of pullbacks of a complex `𝒢^•` on `X_{i₀}`** to the `X_i`, `i ≥ i₀`. -/
abbrev aboveComplexSystem
    (G : CochainComplex (Sheaf (smallEtaleTopology (DX.obj (op i₀))) Ab.{u + 1}) ℤ) :
    EtaleComplexSystem (aboveInclusion i₀ ⋙ DX) :=
  EtaleComplexSystem.ofCocone (D := aboveInclusion i₀ ⋙ DX)
    (fun j : (Set.Ici i₀)ᵒᵖ => DX.map (aboveTransition i₀ j))
    (fun {_ _} c => (map_aboveTransition (DX := DX) i₀ c).symm) G

/-- The pullbacks to the `X_i`, `i ≥ i₀`, of a complex vanishing in degrees `< a` vanish in
degrees `< a`. -/
instance isStrictlyGE_aboveComplexSystem (a : ℤ)
    (G : CochainComplex (Sheaf (smallEtaleTopology (DX.obj (op i₀))) Ab.{u + 1}) ℤ)
    [G.IsStrictlyGE a] (j : (Set.Ici i₀)ᵒᵖ) :
    ((aboveComplexSystem (DX := DX) i₀ G).obj j).IsStrictlyGE a :=
  inferInstanceAs ((((smallEtalePullbackAb (DX.map (aboveTransition i₀ j))).mapHomologicalComplex
    _).obj G).IsStrictlySupported (ComplexShape.embeddingUpIntGE a))

/-- The inverse image of a complex vanishing in degrees `< a` vanishes in degrees `< a`. -/
instance isStrictlyGE_mapHomologicalComplex_smallEtalePullbackAb (a : ℤ) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (G : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ)
    [G.IsStrictlyGE a] :
    CochainComplex.IsStrictlyGE (((smallEtalePullbackAb f).mapHomologicalComplex _).obj G) a :=
  inferInstanceAs ((((smallEtalePullbackAb f).mapHomologicalComplex _).obj G).IsStrictlySupported
    (ComplexShape.embeddingUpIntGE a))

variable (cS) in
/-- The objects `h_i^{-1}R^pg_{i, *}K_i`, `i ≥ i₀`, of the system of 0GIU. -/
abbrev derivedPullbackTerm (p : ℤ) (K₀ : PlusAb (DX.obj (op i₀))) (j : (Set.Ici i₀)ᵒᵖ) :
    Sheaf (smallEtaleTopology cS.pt) Ab.{u + 1} :=
  (smallEtalePullbackAb ((cS.whisker (aboveInclusion i₀)).π.app j)).obj
    ((homologyAb ((aboveInclusion i₀ ⋙ DS).obj j) p).obj
      ((derivedPushforwardAb ((aboveMorphism γ i₀).app j)).obj (aboveLevelPullback i₀ K₀ j)))

variable (cS) in
/-- The transition maps `h_{i'}^{-1}R^pg_{i', *}K_{i'} ⟶ h_i^{-1}R^pg_{i, *}K_i` of the system of
0GIU: the derived base change maps of the transition squares composed with `R^pg_{i, *}` of the
comparisons `R f_{ii'}^{-1}K_{i'} ≅ K_i`, pulled back to `S`. -/
abbrev derivedPullbackTransition (p : ℤ) (K₀ : PlusAb (DX.obj (op i₀))) {j j' : (Set.Ici i₀)ᵒᵖ}
    (c : j ⟶ j') : derivedPullbackTerm γ cS i₀ p K₀ j' ⟶ derivedPullbackTerm γ cS i₀ p K₀ j :=
  (conePullbackComp (cS.whisker (aboveInclusion i₀)) c).inv.app _ ≫
    (smallEtalePullbackAb ((cS.whisker (aboveInclusion i₀)).π.app j)).map
      (derivedTransitionMap (aboveMorphism γ i₀) p c (aboveLevelPullback i₀ K₀ j')
        (aboveLevelPullback i₀ K₀ j) (derivedLevelPullbackComparison i₀ K₀ c))

variable (cX cS) in
/-- The cocone maps `h_i^{-1}R^pg_{i, *}K_i ⟶ R^pg_*K` of 0GIU, for a morphism `g : X ⟶ S` with
`g ≫ h_i = f_i ≫ g_i`: the derived base change maps of the projection squares composed with
`R^pg_*` of the comparisons `R f_i^{-1}K_i ≅ K`. For `g` the limit morphism these are the maps
`Stacks.EtaleCohomology.LimitHigherDirectImage.derivedProjectionMap`. -/
abbrev derivedPullbackLeg (p : ℤ) (K₀ : PlusAb (DX.obj (op i₀))) (g : cX.pt ⟶ cS.pt)
    (w : ∀ j, g ≫ (cS.whisker (aboveInclusion i₀)).π.app j =
      (cX.whisker (aboveInclusion i₀)).π.app j ≫ (aboveMorphism γ i₀).app j)
    (j : (Set.Ici i₀)ᵒᵖ) :
    derivedPullbackTerm γ cS i₀ p K₀ j ⟶
      (homologyAb cS.pt p).obj ((derivedPushforwardAb g).obj
        ((derivedPullbackAb (cX.π.app (op i₀))).obj K₀)) :=
  derivedBaseChangeHomologyMap ((cS.whisker (aboveInclusion i₀)).π.app j)
    ((aboveMorphism γ i₀).app j) g ((cX.whisker (aboveInclusion i₀)).π.app j) (w j) p
    (aboveLevelPullback i₀ K₀ j) _ (derivedLimitPullbackComparison i₀ K₀ j)

variable (cX) in
/-- The cocone maps `h_i^{-1}R^pg_{i, *}ℱ_i^• ⟶ R^pg_*ℱ^•` of 0GIV for the system of pullbacks
of a complex `𝒢^•` on `X_{i₀}`. -/
abbrev aboveComplexLeg
    (G : CochainComplex (Sheaf (smallEtaleTopology (DX.obj (op i₀))) Ab.{u + 1}) ℤ)
    (j : (Set.Ici i₀)ᵒᵖ) :
    ((smallEtalePullbackAb ((cX.whisker (aboveInclusion i₀)).π.app j)).mapHomologicalComplex
        _).obj ((aboveComplexSystem i₀ G).obj j) ⟶
      ((smallEtalePullbackAb (cX.π.app (op i₀))).mapHomologicalComplex _).obj G :=
  EtaleComplexSystem.ofCoconeLeg (D := aboveInclusion i₀ ⋙ DX)
    (fun j : (Set.Ici i₀)ᵒᵖ => DX.map (aboveTransition i₀ j))
    (fun {_ _} c => (map_aboveTransition (DX := DX) i₀ c).symm) G (cX.whisker (aboveInclusion i₀))
    (cX.π.app (op i₀)) (fun j => cX.w (aboveTransition i₀ j)) j

variable (cS) in
/-- The identification of the term of 0GIV for the pullbacks of a complex representing `K_0` with
the term of 0GIU. -/
abbrev aboveComparisonIso (p a : ℤ) (K₀ : PlusAb (DX.obj (op i₀)))
    (G : CochainComplex (Sheaf (smallEtaleTopology (DX.obj (op i₀))) Ab.{u + 1}) ℤ)
    [G.IsStrictlyGE a] (e : K₀ ≅ plusDerivedObj a G) (j : (Set.Ici i₀)ᵒᵖ) :
    (smallEtalePullbackAb ((cS.whisker (aboveInclusion i₀)).π.app j)).obj
        ((complexHigherDirectImageSystem (aboveMorphism γ i₀) p a
          (aboveComplexSystem i₀ G)).obj j) ≅
      derivedPullbackTerm γ cS i₀ p K₀ j :=
  (smallEtalePullbackAb ((cS.whisker (aboveInclusion i₀)).π.app j)).mapIso
    ((homologyAb ((aboveInclusion i₀ ⋙ DS).obj j) p).mapIso
      ((derivedPushforwardAb ((aboveMorphism γ i₀).app j)).mapIso
        (complexPullbackIso a (DX.map (aboveTransition i₀ j)) G e)))

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] in
/-- The identifications `aboveComparisonIso` commute with the transition maps. -/
theorem pullbackDiagramMap_comp_aboveComparisonIso (p a : ℤ) (K₀ : PlusAb (DX.obj (op i₀)))
    (G : CochainComplex (Sheaf (smallEtaleTopology (DX.obj (op i₀))) Ab.{u + 1}) ℤ)
    [G.IsStrictlyGE a] (e : K₀ ≅ plusDerivedObj a G) {j j' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j') :
    (complexHigherDirectImageSystem (aboveMorphism γ i₀) p a
        (aboveComplexSystem i₀ G)).pullbackDiagramMap (cS.whisker (aboveInclusion i₀))
          (i := j) (j := j') c ≫ (aboveComparisonIso γ cS i₀ p a K₀ G e j).hom =
      (aboveComparisonIso γ cS i₀ p a K₀ G e j').hom ≫
        derivedPullbackTransition γ cS i₀ p K₀ c := by
  have k := derivedTransitionMap_naturality (aboveMorphism γ i₀) p c
    (complexTransitionComparison a (aboveComplexSystem i₀ G) c)
    (derivedLevelPullbackComparison i₀ K₀ c)
    (complexPullbackIso a (DX.map (aboveTransition i₀ j')) G e).hom
    (complexPullbackIso a (DX.map (aboveTransition i₀ j)) G e).hom
    (complexPullbackIso_comp a (DX.map (aboveTransition i₀ j'))
      (DX.map ((aboveInclusion i₀).map c)) (DX.map (aboveTransition i₀ j))
      (map_aboveTransition i₀ c) G e)
  have hk := ((smallEtalePullbackAb ((cS.whisker (aboveInclusion i₀)).π.app j)).map_comp
    _ _).symm.trans ((congrArg (smallEtalePullbackAb ((cS.whisker (aboveInclusion i₀)).π.app
      j)).map k.symm).trans
        ((smallEtalePullbackAb ((cS.whisker (aboveInclusion i₀)).π.app j)).map_comp _ _))
  have hn := (conePullbackComp (cS.whisker (aboveInclusion i₀)) c).inv.naturality
    ((homologyAb ((aboveInclusion i₀ ⋙ DS).obj j') p).map
      ((derivedPushforwardAb ((aboveMorphism γ i₀).app j')).map
        (complexPullbackIso a (DX.map (aboveTransition i₀ j')) G e).hom))
  simp only [Functor.comp_map] at hn
  exact comp_comp_eq_of_comp_eq hk hn

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] in
/-- The identifications `aboveComparisonIso` commute with the cocone maps. -/
theorem complexLeg_comp_aboveComparisonIso (p a : ℤ) (K₀ : PlusAb (DX.obj (op i₀)))
    (G : CochainComplex (Sheaf (smallEtaleTopology (DX.obj (op i₀))) Ab.{u + 1}) ℤ)
    [G.IsStrictlyGE a] (e : K₀ ≅ plusDerivedObj a G)
    (hcS' : IsLimit (cS.whisker (aboveInclusion i₀)))
    (j : (Set.Ici i₀)ᵒᵖ) :
    complexLeg (aboveMorphism γ i₀) p a (aboveComplexSystem i₀ G) (cX.whisker (aboveInclusion i₀))
        (cS.whisker (aboveInclusion i₀)) hcS' _ (aboveComplexLeg cX i₀ G) j ≫
      ((homologyAb cS.pt p).mapIso ((derivedPushforwardAb (limitMorphism (aboveMorphism γ i₀)
        (cX.whisker (aboveInclusion i₀)) (cS.whisker (aboveInclusion i₀)) hcS')).mapIso
          (complexPullbackIso a (cX.π.app (op i₀)) G e))).hom =
    (aboveComparisonIso γ cS i₀ p a K₀ G e j).hom ≫
      derivedProjectionMap (aboveMorphism γ i₀) (cX.whisker (aboveInclusion i₀))
        (cS.whisker (aboveInclusion i₀)) hcS' p j (aboveLevelPullback i₀ K₀ j) _
        (derivedLimitPullbackComparison i₀ K₀ j) :=
  (derivedProjectionMap_naturality (aboveMorphism γ i₀) (cX.whisker (aboveInclusion i₀))
    (cS.whisker (aboveInclusion i₀)) hcS' p j
    _ (derivedLimitPullbackComparison i₀ K₀ j)
    (complexPullbackIso a (DX.map (aboveTransition i₀ j)) G e).hom
    (complexPullbackIso a (cX.π.app (op i₀)) G e).hom
    (complexPullbackIso_comp a (DX.map (aboveTransition i₀ j))
      (cX.π.app ((aboveInclusion i₀).obj j))
      (cX.π.app (op i₀)) (cX.w (aboveTransition i₀ j)).symm G e)).symm

include hcX in
/-- **Stacks 0GIU for the systems restricted to the indices above `i₀`**, with the limit
morphism of the restricted systems. -/
theorem derivedPullbackHigherDirectImageColimit_aux (K₀ : PlusAb (DX.obj (op i₀))) (p : ℤ)
    (hcS' : IsLimit (cS.whisker (aboveInclusion i₀))) :
    (∀ {j j' j'' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j') (c' : j' ⟶ j''),
        derivedPullbackTransition γ cS i₀ p K₀ (c ≫ c') =
          derivedPullbackTransition γ cS i₀ p K₀ c' ≫ derivedPullbackTransition γ cS i₀ p K₀ c) ∧
      (∀ {j j' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j'),
        derivedPullbackTransition γ cS i₀ p K₀ c ≫
          derivedProjectionMap (aboveMorphism γ i₀) (cX.whisker (aboveInclusion i₀))
            (cS.whisker (aboveInclusion i₀)) hcS' p j (aboveLevelPullback i₀ K₀ j) _
            (derivedLimitPullbackComparison i₀ K₀ j) =
        derivedProjectionMap (aboveMorphism γ i₀) (cX.whisker (aboveInclusion i₀))
            (cS.whisker (aboveInclusion i₀)) hcS' p j' (aboveLevelPullback i₀ K₀ j') _
            (derivedLimitPullbackComparison i₀ K₀ j')) ∧
      IsSystemColimit (derivedPullbackTerm γ cS i₀ p K₀)
        (fun {j j'} c => derivedPullbackTransition γ cS i₀ p K₀ (j := j) (j' := j') c)
        ((homologyAb cS.pt p).obj ((derivedPushforwardAb (limitMorphism (aboveMorphism γ i₀)
          (cX.whisker (aboveInclusion i₀)) (cS.whisker (aboveInclusion i₀)) hcS')).obj
          ((derivedPullbackAb (cX.π.app (op i₀))).obj K₀)))
        (fun j => derivedProjectionMap (aboveMorphism γ i₀) (cX.whisker (aboveInclusion i₀))
          (cS.whisker (aboveInclusion i₀)) hcS' p j (aboveLevelPullback i₀ K₀ j) _
          (derivedLimitPullbackComparison i₀ K₀ j)) := by
  have : Nonempty (Set.Ici i₀) := ⟨⟨i₀, le_rfl⟩⟩
  let E := aboveInclusion i₀
  have : ∀ {j j' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j'), IsAffineHom ((E ⋙ DX).map c) := fun c =>
    inferInstanceAs (IsAffineHom (DX.map (E.map c)))
  have : ∀ {j j' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j'), IsAffineHom ((E ⋙ DS).map c) := fun c =>
    inferInstanceAs (IsAffineHom (DS.map (E.map c)))
  have : ∀ j, QuasiCompact ((aboveMorphism γ i₀).app j) := fun j =>
    inferInstanceAs (QuasiCompact (γ.app (E.obj j)))
  have : ∀ j, QuasiSeparated ((aboveMorphism γ i₀).app j) := fun j =>
    inferInstanceAs (QuasiSeparated (γ.app (E.obj j)))
  have hcX' := (Functor.Initial.isLimitWhiskerEquiv E cX).symm hcX
  obtain ⟨a, G, _, ⟨e⟩⟩ := exists_iso_plusDerivedObj K₀
  obtain ⟨hcoc, hcol⟩ := complexHigherDirectImageColimit (aboveMorphism γ i₀) hcX' hcS'
    (aboveComplexSystem i₀ G) a
    _ (aboveComplexLeg cX i₀ G)
    (EtaleComplexSystem.isPullbackCocone_ofCocone (D := aboveInclusion i₀ ⋙ DX)
      (fun j : (Set.Ici i₀)ᵒᵖ => DX.map (aboveTransition i₀ j))
      (fun {_ _} c => (map_aboveTransition (DX := DX) i₀ c).symm) G (cX.whisker E)
      (cX.π.app (op i₀)) (fun j => cX.w (aboveTransition i₀ j)))
    (EtaleComplexSystem.isPullbackColimitPresentation_ofCocone (D := aboveInclusion i₀ ⋙ DX)
      (fun j : (Set.Ici i₀)ᵒᵖ => DX.map (aboveTransition i₀ j))
      (fun {_ _} c => (map_aboveTransition (DX := DX) i₀ c).symm) G (cX.whisker E)
      (cX.π.app (op i₀)) (fun j => cX.w (aboveTransition i₀ j))) p
  let θ := aboveComparisonIso γ cS i₀ p a K₀ G e
  let eB := (homologyAb cS.pt p).mapIso ((derivedPushforwardAb (limitMorphism
    (aboveMorphism γ i₀) (cX.whisker E) (cS.whisker E) hcS')).mapIso
      (complexPullbackIso a (cX.π.app (op i₀)) G e))
  have hT := fun {j j' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j') =>
    pullbackDiagramMap_comp_aboveComparisonIso γ (cS := cS) i₀ p a K₀ G e c
  have hψ := fun j => complexLeg_comp_aboveComparisonIso γ (cX := cX) (cS := cS) i₀ p a K₀ G e
    hcS' j
  exact ⟨fun {j j' j''} c c' => comp_eq_of_iso (θ j) (θ j') (θ j'') (hT c) (hT c') (hT (c ≫ c'))
      ((complexHigherDirectImageSystem (aboveMorphism γ i₀) p a
        (aboveComplexSystem i₀ G)).pullbackDiagramMap_comp (cS.whisker E) c c'),
    fun c => cocone_of_isoSystem θ eB hT hψ hcoc c,
    (IsSystemColimit.iff_of_isoSystem θ eB hT hψ).1 hcol⟩

include hcX hcS in
/-- Let `I` be a directed set, `g_i : X_i ⟶ S_i` an inverse system of
quasi-compact and quasi-separated morphisms of schemes with affine transition morphisms
`f_{i'i}`, `h_{i'i}`, and `g : X ⟶ S` its limit with projections `f_i`, `h_i`. Let `0 = i₀ ∈ I`,
`K_0 ∈ D^+(X_{0, étale})`, `K_i = R f_{i0}^{-1}K_0` its pullback to `X_i` for `i ≥ 0` and
`K = R f_0^{-1}K_0` its pullback to `X`. Then for every `p ∈ ℤ` the maps
`h_{i'i}^{-1}R^pg_{i, *}K_i ⟶ R^pg_{i', *}K_{i'}` (the derived base change maps of the
transition squares composed with `R^pg_{i', *}` of `R f_{i'i}^{-1}K_i ≅ K_{i'}`), pulled back to
`S`, satisfy the cocycle condition, the maps `h_i^{-1}R^pg_{i, *}K_i ⟶ R^pg_*K` (the derived base
change maps of the projection squares composed with `R^pg_*` of `R f_i^{-1}K_i ≅ K`) are
compatible with them, and they present `R^pg_*K = colim_{i ≥ 0} h_i^{-1}R^pg_{i, *}K_i`. -/
@[stacks 0GIU, sga "4 VII 5.11" "more general"]
theorem derivedPullbackHigherDirectImageColimit (K₀ : PlusAb (DX.obj (op i₀))) (p : ℤ) :
    (∀ {j j' j'' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j') (c' : j' ⟶ j''),
        derivedPullbackTransition γ cS i₀ p K₀ (c ≫ c') =
          derivedPullbackTransition γ cS i₀ p K₀ c' ≫ derivedPullbackTransition γ cS i₀ p K₀ c) ∧
      (∀ {j j' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j'),
        derivedPullbackTransition γ cS i₀ p K₀ c ≫ derivedPullbackLeg γ cX cS i₀ p K₀
            (limitMorphism γ cX cS hcS)
            (fun j => limitMorphism_comp_π γ cX cS hcS ((aboveInclusion i₀).obj j)) j =
          derivedPullbackLeg γ cX cS i₀ p K₀ (limitMorphism γ cX cS hcS)
            (fun j => limitMorphism_comp_π γ cX cS hcS ((aboveInclusion i₀).obj j)) j') ∧
      IsSystemColimit (derivedPullbackTerm γ cS i₀ p K₀)
        (fun {j j'} c => derivedPullbackTransition γ cS i₀ p K₀ (j := j) (j' := j') c)
        ((homologyAb cS.pt p).obj ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).obj
          ((derivedPullbackAb (cX.π.app (op i₀))).obj K₀)))
        (derivedPullbackLeg γ cX cS i₀ p K₀ (limitMorphism γ cX cS hcS)
          (fun j => limitMorphism_comp_π γ cX cS hcS ((aboveInclusion i₀).obj j))) := by
  let E := aboveInclusion i₀
  have hcS' := (Functor.Initial.isLimitWhiskerEquiv E cS).symm hcS
  have hg : limitMorphism (aboveMorphism γ i₀) (cX.whisker E) (cS.whisker E) hcS' =
      limitMorphism γ cX cS hcS :=
    hcS'.hom_ext fun j => (limitMorphism_comp_π _ _ _ hcS' j).trans
      (limitMorphism_comp_π γ cX cS hcS (E.obj j)).symm
  obtain ⟨h₁, h₂, h₃⟩ := derivedPullbackHigherDirectImageColimit_aux γ hcX i₀ K₀ p hcS'
  have key : ∀ (h : cX.pt ⟶ cS.pt)
      (_ : limitMorphism (aboveMorphism γ i₀) (cX.whisker E) (cS.whisker E) hcS' = h)
      (w : ∀ j, h ≫ (cS.whisker E).π.app j = (cX.whisker E).π.app j ≫ (aboveMorphism γ i₀).app j),
      (∀ {j j' : (Set.Ici i₀)ᵒᵖ} (c : j ⟶ j'),
        derivedPullbackTransition γ cS i₀ p K₀ c ≫ derivedPullbackLeg γ cX cS i₀ p K₀ h w j =
          derivedPullbackLeg γ cX cS i₀ p K₀ h w j') ∧
      IsSystemColimit (derivedPullbackTerm γ cS i₀ p K₀)
        (fun {j j'} c => derivedPullbackTransition γ cS i₀ p K₀ (j := j) (j' := j') c)
        ((homologyAb cS.pt p).obj ((derivedPushforwardAb h).obj
          ((derivedPullbackAb (cX.π.app (op i₀))).obj K₀)))
        (derivedPullbackLeg γ cX cS i₀ p K₀ h w) := by
    rintro h rfl w
    obtain rfl : w = fun j => limitMorphism_comp_π (aboveMorphism γ i₀) (cX.whisker E)
      (cS.whisker E) hcS' j := rfl
    exact ⟨fun c => h₂ c, h₃⟩
  obtain ⟨k₁, k₂⟩ := key _ hg (fun j => limitMorphism_comp_π γ cX cS hcS _)
  exact ⟨fun c c' => h₁ c c', fun c => k₁ c, k₂⟩

end Main

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
