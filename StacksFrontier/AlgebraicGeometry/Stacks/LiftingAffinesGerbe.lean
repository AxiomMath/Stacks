module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAmbientComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCartesianLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleSmoothLift
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesIsStack
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Defs

/-! # The category of smooth lifts is a gerbe (Stacks 0CJX)

Fix a thickening `ι : 𝒳 ⟶ 𝒳'` of algebraic stacks over `S`, an algebraic space `W` and a smooth
1-morphism `x : W ⟶ 𝒳`. Stacks 0CJX says that the category `p : 𝒞 ⟶ W_{spaces,étale}` of smooth
lifts of étale opens of `W` (**Stacks 0CJP**, `AlgebraicGeometry.Stack.EtaleSmoothLift`, with
projection `AlgebraicGeometry.Stack.EtaleSmoothLift.proj`) is a gerbe (**Stacks 06NZ**,
`CategoryTheory.Functor.IsGerbe`). The source's proof: it is a stack in groupoids by
**Stacks 0CJU**; condition (2) of 06NZ (local existence of objects) follows from **Stacks 0CJV**,
and condition (3) (local connectedness) follows from **Stacks 0CJW**.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.isGerbe_proj`: the category of smooth lifts is a
  gerbe (**Stacks 0CJX**).
* `AlgebraicGeometry.Stack.EtaleSmoothLift.locallyNonempty_proj`: condition (2), from 0CJV.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.locallyConnected_proj`: condition (3), from 0CJW.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.exists_sieve_nonempty_fiber_of_isEtaleCovering`:
  condition (2) over one étale open `U`, from a covering of `U` by smooth lifts for `x ∘ a`, which
  is what 0CJV provides once applied to `U ⟶ W ⟶ 𝒳`.

## Constructions

* `AlgebraicGeometry.Stack.EtaleSmoothLift.ofEtaleOpen`: a smooth lift of an étale open of `U`
  (for `x ∘ a`, where `a : U ⟶ W` is étale) is a smooth lift of an étale open of `W`.
* `AlgebraicGeometry.Stack.EtaleSmoothLift.ofIsPullback`: the smooth lift cut out of `ξ` by an
  étale morphism `f' : V' ⟶ U'` of ambient spaces with `V = U ×_{U'} V'`, with its morphism
  `ofIsPullbackHom` to `ξ` (the construction of `f^*ξ` in the proof of Stacks 0CJT, with the
  ambient space given), and `ofIsPullbackHomOf`, a morphism to a second smooth lift `η` from an
  étale `f'' : V' ⟶ U''` and a 2-isomorphism `y' ∘ f'' ≅ x' ∘ f'` restricting to the comparison of
  the fillers — exactly the output of Stacks 0CJW.

## References

* [Stacks Project, Tag 06NZ](https://stacks.math.columbia.edu/tag/06NZ)
* [Stacks Project, Tag 0CJP](https://stacks.math.columbia.edu/tag/0CJP)
* [Stacks Project, Tag 0CJT](https://stacks.math.columbia.edu/tag/0CJT)
* [Stacks Project, Tag 0CJU](https://stacks.math.columbia.edu/tag/0CJU)
* [Stacks Project, Tag 0CJV](https://stacks.math.columbia.edu/tag/0CJV)
* [Stacks Project, Tag 0CJW](https://stacks.math.columbia.edu/tag/0CJW)
* [Stacks Project, Tag 0CJX](https://stacks.math.columbia.edu/tag/0CJX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

universe u w t

namespace CategoryTheory

/-- **Inverting a coherence identity between transported isomorphisms, with a middle
transport.** If `Γ` is `v⁻¹ ≫ u` read along transports, then `u` followed by `Γ⁻¹` is `v`, read
along transports. -/
theorem eqToHom_comp_hom_comp_eqToHom_comp_inv_of_eqToHom {C : Type*} [Category C]
    {L₀ L₁ L₂ P₁ P₂ Q₁ Q₂ : C} (a : L₀ = L₁) (a₂ : L₀ = L₂) (b : P₁ = P₂) (c₁ : Q₂ = Q₁)
    (c₂ : P₁ = P₂) (e : L₂ = L₁) (u : L₁ ≅ P₁) (v : L₂ ≅ Q₁) (Γ : Q₂ ≅ P₂)
    (hΓ : Γ.hom = eqToHom c₁ ≫ v.inv ≫ eqToHom e ≫ u.hom ≫ eqToHom c₂) :
    (eqToHom a ≫ u.hom ≫ eqToHom b) ≫ Γ.inv = eqToHom a₂ ≫ v.hom ≫ eqToHom c₁.symm := by
  subst a a₂ b c₁
  have hΓ' : Γ = v.symm ≪≫ u := Iso.ext (by simpa using hΓ)
  subst hΓ'
  simp

end CategoryTheory

namespace AlgebraicGeometry.Space.SpacesEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **A jointly point-surjective family generates a covering sieve of the spaces-étale site.** -/
theorem ofArrows_mem_topology {U : SpacesEtale B S hS X} {I : Type (u + 1)}
    (V : I → SpacesEtale B S hS X) (f : ∀ i, V i ⟶ U)
    (h : ∀ p : points B S hS ((toSpaces B S hS X).obj U).1, ∃ i,
      ∃ y : points B S hS ((toSpaces B S hS X).obj (V i)).1,
        pointsMap B S hS ((toSpaces B S hS X).obj (V i)).1
          ((toSpaces B S hS X).map (f i)).hom y = p) :
    Sieve.ofArrows V f ∈ topology B S hS X U :=
  Precoverage.generate_mem_toGrothendieck (⟨⟨I, V, f⟩, rfl, h⟩ :
    Presieve.ofArrows V f ∈ precoverage B S hS X U)

end AlgebraicGeometry.Space.SpacesEtale

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- The composite `U ⟶ W ⟶ 𝒳` of an étale open of `W` with the smooth `x` is smooth. -/
theorem isSmooth_map_comp (hx : AlgebraicStacks.IsSmooth B S hS x)
    (U : Space.SpacesEtale B S hS W) :
    AlgebraicStacks.IsSmooth B S hS ((algebraicSpaceStackFunctor B S hS).map U.obj.hom ≫ x) :=
  AlgebraicStacks.isSmooth_comp B S hS _ _
    ((isSmooth_algebraicSpaceStackMap_iff.{u, w} B S hS U.obj.left.property W.property
      U.obj.hom.hom).2 (Space.isSmooth_of_isEtale B S hS W.property U.property)) hx

/-- A smooth lift of an étale open of `U` (for `x ∘ a`) is a smooth lift of an étale open of
`W` (for `x`). -/
def ofEtaleOpen (hx : AlgebraicStacks.IsSmooth B S hS x) {U : Space.SpacesEtale B S hS W}
    {hxU : AlgebraicStacks.IsSmooth B S hS ((algebraicSpaceStackFunctor B S hS).map U.obj.hom ≫ x)}
    (ξ : EtaleSmoothLift B S hS ι hι U.obj.left
      ((algebraicSpaceStackFunctor B S hS).map U.obj.hom ≫ x) hxU) :
    EtaleSmoothLift B S hS ι hι W x hx where
  base := ⟨Over.mk (ξ.base.obj.hom ≫ U.obj.hom),
    Space.isEtale_comp B S hS ξ.base.property U.property⟩
  ambient := ξ.ambient
  inclusion := ξ.inclusion
  ambientMap := ξ.ambientMap
  isSmooth_ambientMap := ξ.isSmooth_ambientMap
  comm := ξ.comm
  isTwoFibreProduct := ξ.isTwoFibreProduct

/-- The structure morphism of `ofEtaleOpen ξ` to the étale open `U`. -/
def ofEtaleOpenBase (hx : AlgebraicStacks.IsSmooth B S hS x) {U : Space.SpacesEtale B S hS W}
    {hxU : AlgebraicStacks.IsSmooth B S hS ((algebraicSpaceStackFunctor B S hS).map U.obj.hom ≫ x)}
    (ξ : EtaleSmoothLift B S hS ι hι U.obj.left
      ((algebraicSpaceStackFunctor B S hS).map U.obj.hom ≫ x) hxU) :
    (ofEtaleOpen hx ξ).base ⟶ U :=
  ObjectProperty.homMk (Over.homMk ξ.base.obj.hom rfl)

section OfIsPullback

variable (ξ : EtaleSmoothLift B S hS ι hι W x hx) {V : Space.SpacesEtale B S hS W}
  (f : V ⟶ ξ.base) {V' : AlgebraicSpaces B S hS} (j : V.obj.left ⟶ V') (f' : V' ⟶ ξ.ambient)
  (hf' : Space.IsEtale B S hS f'.hom) (hpb : IsPullback j f.hom.left f' ξ.inclusion)

/-- The filler of the smooth lift `ofIsPullback`: `α` whiskered by `f`. -/
def ofIsPullbackComm :
    ((algebraicSpaceStackFunctor B S hS).map V.obj.hom ≫ x) ≫ ι ≅
      (algebraicSpaceStackFunctor B S hS).map j ≫
        ((algebraicSpaceStackFunctor B S hS).map f' ≫ ξ.ambientMap) :=
  eqToIso (congrArg (fun p => (p ≫ x) ≫ ι) (show (algebraicSpaceStackFunctor.{u, w} B S hS).map
      V.obj.hom = (algebraicSpaceStackFunctor.{u, w} B S hS).map f.hom.left ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map ξ.base.obj.hom by
      rw [← Functor.map_comp, Over.w f.hom])) ≪≫
    whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map f.hom.left) ξ.comm ≪≫
      eqToIso (congrArg (· ≫ ξ.ambientMap) (show
        (algebraicSpaceStackFunctor.{u, w} B S hS).map f.hom.left ≫
          (algebraicSpaceStackFunctor.{u, w} B S hS).map ξ.inclusion =
        (algebraicSpaceStackFunctor.{u, w} B S hS).map j ≫
          (algebraicSpaceStackFunctor.{u, w} B S hS).map f' by
        rw [← Functor.map_comp, ← Functor.map_comp, hpb.w]))

/-- **The smooth lift cut out of `ξ` by an étale morphism of ambient spaces.** Given a smooth lift
`ξ = (U, U', i, x', α)`, a morphism `f : V ⟶ U` of the spaces-étale site of `W` and an étale
`f' : V' ⟶ U'` with `V = U ×_{U'} V'` (through `j : V ⟶ V'`), the smooth lift
`(V, V', j, x' ∘ f', f^*α)`. This is the construction of `f^*ξ` in the proof of Stacks 0CJT, with
the ambient space given. -/
def ofIsPullback : EtaleSmoothLift B S hS ι hι W x hx :=
  have hTw : (algebraicSpaceStackFunctor.{u, w} B S hS).map f.hom.left ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map ξ.inclusion =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map j ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map f' := by
    rw [← Functor.map_comp, ← Functor.map_comp, hpb.w]
  have hpb' := AlgebraicSpaces.isPullback_hom B S hS hpb.flip
  have ha : (algebraicSpaceStackFunctor B S hS).map V.obj.hom ≫ x =
      (algebraicSpaceStackFunctor B S hS).map f.hom.left ≫
        ((algebraicSpaceStackFunctor B S hS).map ξ.base.obj.hom ≫ x) :=
    congrArg (· ≫ x) (show (algebraicSpaceStackFunctor.{u, w} B S hS).map V.obj.hom =
      (algebraicSpaceStackFunctor.{u, w} B S hS).map f.hom.left ≫
        (algebraicSpaceStackFunctor.{u, w} B S hS).map ξ.base.obj.hom by
      rw [← Functor.map_comp, Over.w f.hom])
  have hT := isTwoFibreProduct_algebraicSpaceStackSquare.{u, w} B S hS ξ.base.obj.left.property
      V'.property ξ.ambient.property V.obj.left.property hpb'
  have hsm : AlgebraicStacks.IsSmooth B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map f') :=
    (isSmooth_algebraicSpaceStackMap_iff.{u, w} B S hS V'.property ξ.ambient.property f'.hom).2
      (Space.isSmooth_of_isEtale B S hS ξ.ambient.property hf')
  { base := V
    ambient := V'
    inclusion := j
    ambientMap := (algebraicSpaceStackFunctor B S hS).map f' ≫ ξ.ambientMap
    isSmooth_ambientMap := AlgebraicStacks.isSmooth_comp B S hS _ _ hsm ξ.isSmooth_ambientMap
    comm := ofIsPullbackComm ξ f j f' hpb
    isTwoFibreProduct := Bicategory.isTwoFibreProduct_of_paste_of_eqToHom _
      ξ.isTwoFibreProduct _ hT hTw ((subsingleton_hom₂_algebraicSpaceStackFunctor_obj _ _).elim _ _)
      ha _ rfl }

/-- The morphism `ofIsPullback ξ f j f' ⟶ ξ` lying over `f`, with ambient component `f'` and an
identity comparison 2-morphism. -/
def ofIsPullbackHom : ofIsPullback ξ f j f' hf' hpb ⟶ ξ where
  base := f
  ambient := f'
  inclusion_comp := hpb.w
  comm := 𝟙 _
  coherence := (congrArg ((ofIsPullbackComm ξ f j f' hpb).hom ≫ ·) (whiskerLeft_id _ _)).trans
    (Category.comp_id _)

/-- The equality `x ∘ a_η ∘ f_η = x ∘ a_ξ ∘ f` behind the comparison in
`ofIsPullbackHomOf`: both sides are `x` composed with the structure morphism of `V`. -/
theorem left_leg_eq (η : EtaleSmoothLift B S hS ι hι W x hx) (fη : V ⟶ η.base) :
    (algebraicSpaceStackFunctor B S hS).map fη.hom.left ≫
        (((algebraicSpaceStackFunctor B S hS).map η.base.obj.hom ≫ x) ≫ ι) =
      (algebraicSpaceStackFunctor B S hS).map f.hom.left ≫
        (((algebraicSpaceStackFunctor B S hS).map ξ.base.obj.hom ≫ x) ≫ ι) :=
  congrArg (fun m => ((algebraicSpaceStackFunctor B S hS).map m ≫ x) ≫ ι)
    ((Over.w fη.hom).trans (Over.w f.hom).symm)

/-- **A morphism out of `ofIsPullback` given a second étale ambient morphism.** For a smooth lift
`η`, a morphism `f_η : V ⟶ η.base` and an étale `f'' : V' ⟶ η.ambient` restricting to `f_η`,
a 2-isomorphism `γ : y' ∘ f'' ≅ x' ∘ f'` whose restriction to `V` is the comparison
`f_η^*β⁻¹ ∘ f^*α` of the two fillers defines a morphism `ofIsPullback ξ f j f' ⟶ η` lying over
`f_η`, with ambient component `f''` and comparison `γ⁻¹`. -/
def ofIsPullbackHomOf (η : EtaleSmoothLift B S hS ι hι W x hx) (fη : V ⟶ η.base)
    (f'' : V' ⟶ η.ambient) (hfη : j ≫ f'' = fη.hom.left ≫ η.inclusion)
    (γ : (algebraicSpaceStackFunctor B S hS).map f'' ≫ η.ambientMap ≅
      (algebraicSpaceStackFunctor B S hS).map f' ≫ ξ.ambientMap)
    (hγ : (algebraicSpaceStackFunctor B S hS).map j ◁ γ.hom =
      eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq hfη η.ambientMap) ≫
        ((algebraicSpaceStackFunctor B S hS).map fη.hom.left ◁ η.comm.inv) ≫
          eqToHom (left_leg_eq ξ f η fη) ≫
            ((algebraicSpaceStackFunctor B S hS).map f.hom.left ◁ ξ.comm.hom) ≫
              eqToHom (algebraicSpaceStackFunctor_map_comp_whisker_eq hpb.w.symm ξ.ambientMap)) :
    ofIsPullback ξ f j f' hf' hpb ⟶ η where
  base := fη
  ambient := f''
  inclusion_comp := hfη
  comm := γ.inv
  coherence := eqToHom_comp_hom_comp_eqToHom_comp_inv_of_eqToHom
    (left_leg (ofIsPullback ξ f j f' hf' hpb) ξ f) (left_leg (ofIsPullback ξ f j f' hf' hpb) η fη)
    (algebraicSpaceStackFunctor_map_comp_whisker_eq hpb.w.symm ξ.ambientMap) _ _ _
    (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map f.hom.left) ξ.comm)
    (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map fη.hom.left) η.comm)
    (whiskerLeftIso ((algebraicSpaceStackFunctor B S hS).map j) γ) hγ

/-- The base of `ofIsPullback` is the given étale open `V`. -/
@[simp]
theorem ofIsPullback_base : (ofIsPullback ξ f j f' hf' hpb).base = V := rfl

/-- The morphism `ofIsPullbackHom` lies over the given `f`. -/
@[simp]
theorem ofIsPullbackHom_base : Hom.base (ofIsPullbackHom ξ f j f' hf' hpb) = f := rfl

end OfIsPullback

/-! ### Condition (2) of Stacks 06NZ: local existence of objects -/

/-- An object of the fibre of `proj` over `V`, from any morphism into a smooth lift lying over
an arrow out of `V`. -/
theorem nonempty_fiber_of_hom {V : Space.SpacesEtale B S hS W}
    (ξ : EtaleSmoothLift B S hS ι hι W x hx) (a : V ⟶ ξ.base) :
    Nonempty ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber V) := by
  obtain ⟨η, φ, hφ⟩ := exists_hom_isHomLift ξ a
  exact ⟨⟨η, IsHomLift.domain_eq _ a φ⟩⟩

/-- **Local existence of objects from an étale covering by smooth lifts.** If the étale open `U`
of `W` is covered by the bases of smooth lifts of étale opens of `U` (for `x ∘ a`), then the fibre
of `proj` is nonempty along every arrow of a covering sieve of `U`. -/
theorem exists_sieve_nonempty_fiber_of_isEtaleCovering {U : Space.SpacesEtale B S hS W}
    {hxU : AlgebraicStacks.IsSmooth B S hS ((algebraicSpaceStackFunctor B S hS).map U.obj.hom ≫ x)}
    {J : Type (u + 1)}
    (ξ : J → EtaleSmoothLift B S hS ι hι U.obj.left
      ((algebraicSpaceStackFunctor B S hS).map U.obj.hom ≫ x) hxU)
    (hcov : Space.IsEtaleCovering B S hS (fun j => ((ξ j).base.obj.left).obj)
      (fun j => ((ξ j).base.obj.hom).hom)) :
    ∃ R ∈ Space.SpacesEtale.topology B S hS W U, ∀ ⦃V : Space.SpacesEtale B S hS W⦄ (f : V ⟶ U),
      R f → Nonempty ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber V) := by
  refine ⟨Sieve.ofArrows (fun j => (ofEtaleOpen hx (ξ j)).base)
    (fun j => ofEtaleOpenBase hx (ξ j)), Space.SpacesEtale.ofArrows_mem_topology _ _ ?_, ?_⟩
  · intro p
    obtain ⟨j, y, hy⟩ := Set.mem_iUnion.1 (hcov.jointly_surjective ▸ Set.mem_univ p)
    exact ⟨j, y, hy⟩
  · intro V f hf
    obtain ⟨j, a, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
    exact nonempty_fiber_of_hom (ofEtaleOpen hx (ξ j)) a

/-- **Stacks 06NZ (2) for the smooth lifts of étale opens.** Every étale open `U` of `W` has a
covering along whose members the category of smooth lifts has an object. As in the source, this
is **Stacks 0CJV** applied to the smooth composite `U ⟶ W ⟶ 𝒳`: it covers `U` by the bases of
smooth lifts for `x ∘ a`, which are smooth lifts for `x` through
`AlgebraicGeometry.Stack.EtaleSmoothLift.ofEtaleOpen`. -/
theorem locallyNonempty_proj :
    Functor.LocallyNonempty (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)
      (Space.SpacesEtale.topology B S hS W) := fun U => by
  obtain ⟨J, ξ, hcov⟩ :=
    exists_isEtaleCovering_etaleSmoothLift B S hS ι hι U.obj.left _ (isSmooth_map_comp hx U)
  exact exists_sieve_nonempty_fiber_of_isEtaleCovering ξ hcov

/-! ### Condition (3) of Stacks 06NZ: local connectedness -/

/-- **Local connectedness from smooth lifts with two morphisms.** Given objects `ξ`, `η` over
`U` and, for each member of a covering family of `U`, a smooth lift with morphisms to `ξ` and to
`η` lying over that member, the restrictions of `ξ` and `η` are isomorphic along every arrow of a
covering sieve of `U`. -/
theorem exists_sieve_iso_of_homs {U : Space.SpacesEtale B S hS W}
    (ξ η : EtaleSmoothLift B S hS ι hι W x hx) {K : Type (u + 1)}
    (ζ : K → EtaleSmoothLift B S hS ι hι W x hx) (f : ∀ k, (ζ k).base ⟶ U)
    (m₁ : ∀ k, ζ k ⟶ ξ) (m₂ : ∀ k, ζ k ⟶ η)
    (h₁ : ∀ k, (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (f k) (m₁ k))
    (h₂ : ∀ k, (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (f k) (m₂ k))
    (hcov : ∀ p : Space.points B S hS ((Space.SpacesEtale.toSpaces B S hS W).obj U).1, ∃ k,
      ∃ y : Space.points B S hS ((Space.SpacesEtale.toSpaces B S hS W).obj (ζ k).base).1,
        Space.pointsMap B S hS ((Space.SpacesEtale.toSpaces B S hS W).obj (ζ k).base).1
          ((Space.SpacesEtale.toSpaces B S hS W).map (f k)).hom y = p) :
    ∃ R ∈ Space.SpacesEtale.topology B S hS W U, ∀ ⦃V : Space.SpacesEtale B S hS W⦄ (g : V ⟶ U),
      R g → ∃ (x₁ y₁ : EtaleSmoothLift B S hS ι hι W x hx) (φ₁ : x₁ ⟶ ξ) (υ : y₁ ⟶ η)
        (e : x₁ ≅ y₁), (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g φ₁ ∧
          (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g υ ∧
          (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (𝟙 V) e.hom := by
  refine ⟨Sieve.ofArrows (fun k => (ζ k).base) f,
    Space.SpacesEtale.ofArrows_mem_topology _ _ hcov, ?_⟩
  intro V g hg
  obtain ⟨k, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  obtain ⟨ζ', χ, hχ⟩ := exists_hom_isHomLift (ζ k) a
  have hd := IsHomLift.domain_eq (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) a χ
  exact ⟨ζ', ζ', χ ≫ m₁ k, χ ≫ m₂ k, Iso.refl _, inferInstance, inferInstance,
    IsHomLift.of_fac _ (𝟙 V) (𝟙 ζ') hd hd (by simp)⟩

/-- **Stacks 06NZ (3) for the smooth lifts of étale opens.** Two smooth lifts `ξ`, `η` over the
same étale open `U` of `W` become isomorphic on the members of a covering of `U`. As in the source,
this is **Stacks 0CJW** applied to the two cartesian squares `U = 𝒳 ×_{𝒳'} U'` and
`U = 𝒳 ×_{𝒳'} U''` of `ξ` and `η`: it gives an étale covering `{f'_k : U'_k ⟶ U'}`, étale
`f''_k : U'_k ⟶ U''` and `γ_k : y' ∘ f''_k ≅ x' ∘ f'_k` restricting to the comparison of the two
fillers over `U_k = (f'_k)⁻¹(U) = (f''_k)⁻¹(U)`. The smooth lift `(U_k, U'_k, x' ∘ f'_k)` then maps
to `ξ` through `f'_k` and to `η` through `f''_k` and `γ_k⁻¹`, and the `U_k` cover `U` because the
`U'_k` cover `U'`. -/
theorem locallyConnected_proj :
    Functor.LocallyConnected (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)
      (Space.SpacesEtale.topology B S hS W) := by
  intro U ξ η hξ hη
  subst hξ
  obtain ⟨b, A, i, y, hy, β, hβ⟩ := η
  obtain rfl : b = ξ.base := hη
  obtain ⟨K, V, f', f'', γ, hcov, -, hk⟩ := exists_isEtaleCovering_ambientComparison
    hι (isSmooth_map_comp hx ξ.base) ξ.isSmooth_ambientMap hy ξ.isTwoFibreProduct hβ
  choose Uk e g h₁ h₂ hc using hk
  have hg : ∀ k, Space.IsEtale B S hS (g k).hom := fun k =>
    Space.isEtale_of_isPullback B S hS _ _ _ _ (h₁ k).flip (hcov.etale k)
  let Vk : K → Space.SpacesEtale B S hS W := fun k =>
    ⟨Over.mk (g k ≫ ξ.base.obj.hom), Space.isEtale_comp B S hS (hg k) ξ.base.property⟩
  let fk : ∀ k, Vk k ⟶ ξ.base := fun k => ObjectProperty.homMk (Over.homMk (g k) rfl)
  let m₁ : ∀ k, ofIsPullback ξ (fk k) (e k) (f' k) (hcov.etale k) (h₁ k).flip ⟶ ξ := fun k =>
    ofIsPullbackHom ξ (fk k) (e k) (f' k) (hcov.etale k) (h₁ k).flip
  let m₂ : ∀ k, ofIsPullback ξ (fk k) (e k) (f' k) (hcov.etale k) (h₁ k).flip ⟶
      (⟨ξ.base, A, i, y, hy, β, hβ⟩ : EtaleSmoothLift B S hS ι hι W x hx) := fun k =>
    ofIsPullbackHomOf ξ (fk k) (e k) (f' k) (hcov.etale k) (h₁ k).flip _ (fk k) (f'' k)
      (h₂ k).w.symm (γ k) (by
        refine (hc k).trans ?_
        simp only [whiskerLeft_comp, eqToHom_refl, Category.id_comp, Category.assoc]
        rfl)
  refine exists_sieve_iso_of_homs ξ _ _ fk m₁ m₂ (fun k => inferInstanceAs
    ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (proj.map (m₁ k)) (m₁ k)))
    (fun k => inferInstanceAs
    ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (proj.map (m₂ k)) (m₂ k))) ?_
  intro p
  obtain ⟨k, z, hz⟩ := Set.mem_iUnion.1 (hcov.jointly_surjective ▸ Set.mem_univ
    (Space.pointsMap B S hS ξ.base.obj.left.obj ξ.inclusion.hom p))
  obtain ⟨w, hw, -⟩ := Space.exists_point_of_isPullback B S hS (h₁ k) p z hz.symm
  exact ⟨k, w, hw⟩

/-! ### Stacks 0CJX -/

/-- The category `p : 𝒞 ⟶ W_{spaces, étale}` of smooth lifts of étale opens of `W` along the
thickening `ι : 𝒳 ⟶ 𝒳'` constructed in Stacks 0CJP is a gerbe (Stacks 06NZ), for covering
families indexed by an arbitrary universe `t` in the stack condition. -/
@[stacks 0CJX]
theorem isGerbe_proj :
    Functor.IsGerbe.{t} (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _)
      (Space.SpacesEtale.topology B S hS W) :=
  ⟨isStackInGroupoids_proj, locallyNonempty_proj, locallyConnected_proj⟩

end EtaleSmoothLift

end AlgebraicGeometry.Stack
