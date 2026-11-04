module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPullbackTransport
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluingSlice

/-!
# Morphisms of Frobenius-colimit modules glue along an open cover

The stack condition that condition (1) of Stacks 0EX9 asks of Stacks Tag 0EXE has, at a single
Zariski family, a separated half and a *prestack* half: the canonical descent functor of
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` has to be faithful and full. The
separated half is
`AlgebraicGeometry.faithful_toDescentData_frobeniusColimitModulePseudofunctor`; this file supplies
the gluing of morphisms that the full half rests on, in the transition-functor spelling that the
pseudofunctor speaks.

Two steps are needed, and neither was in the development.

* The gluing itself, `Stacks.SheafOfModules.existsUnique_hom_of_over`, is stated for a covering
  family indexed by a type of the *site's own* universe, while the families of the big h category
  over `S` are indexed by a type of `Type (u + 1)`. The index universe is freed here.
* The gluing is stated for the slice restrictions `M.over V`, while the transition functors of
  Stacks Tag 0EXE are extension of scalars along the canonical morphisms of Frobenius-colimit
  sheaves. The two are identified by
  `AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback`, which is a comparison of
  *functors*; what a Hom-level statement needs is the induced bijection on morphisms, and that
  bijection is what makes the open-subscheme equivalence invisible in the conclusion.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver`: **morphisms of the slice restrictions
  `M.over V ⟶ N.over V` are the same as morphisms of the extensions of scalars along `V.ι`.**
* `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOfFactor` and
  `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion`: the same bijection read along
  a morphism factoring isomorphically through an open, respectively along an open immersion and
  its own image. The second is the form the members of a Zariski family of the big h category over
  `S` present — open immersions of schemes, not inclusions of opens.

## Main results

* `Stacks.SheafOfModules.existsUnique_hom_of_over_of_cover`:
  `Stacks.SheafOfModules.existsUnique_hom_of_over` with the index type of the covering family in
  an arbitrary universe.
* `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver_apply_overFunctor_map`: the bijection
  carries the slice restriction of a global morphism to its extension of scalars, which is what
  makes it usable on both sides of a gluing statement.
* `AlgebraicGeometry.existsUnique_frobeniusColimitPullback_map_eq`: **morphisms of sheaves of
  `colim_F 𝒪_X`-modules given over the members of an open cover of `X` and agreeing on overlaps
  glue to a unique global morphism, in the transition-functor spelling.** The data is given on
  both sides of the bijection, which is not a weakening — see the implementation notes.
* `AlgebraicGeometry.existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion`: **the same
  along a family of open immersions whose images cover `X`** — the shape the full half of the
  stack condition for `AlgebraicGeometry.frobeniusColimitModulePseudofunctor` at a Zariski family
  of the big h category over `S` consumes.
* `AlgebraicGeometry.existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion_of_isBasis`:
  **the same with the compatibility available only over the members of a prescribed basis** — the
  shape the final Zariski glueing of [Stacks, Tag 0EXD] over the basic opens of an affine base
  consumes.

## Implementation notes

**The index shrink carries no transport.** Reindexing a covering family by the *set of opens it
hits* would force a transport of each given morphism along an equality `V i = W` of opens, and
the components of a transported morphism of sheaves of modules are not the components of the
original one. The family used instead is `W ↦ V (σ W)` for a choice `σ` of index realising each
open in the range, so that the given morphism at `σ W` is reused on the nose; the only thing
proved about `σ` is that `V (σ W) = W`, and it is used solely to see that the reindexed family
still covers and that the conclusion at an arbitrary `i` follows. That last step compares two
morphisms whose *types* differ by such an equality, and it is therefore made componentwise —
which is exactly where the overlap hypothesis, taken at `W = V i`, is available.

**Why a bijection and not a rewrite.**
`AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback` cannot be rewritten with: the two
functors it compares differ at the level of the sheaf of rings as well as the site, and `rw` would
have to build a motive over a goal mentioning free and unit modules on a scheme, where
`AlgebraicGeometry.Scheme.ringCatSheaf` does not unfold at the transparency a motive is built at.
The comparison is therefore used through `CategoryTheory.Iso.homCongr`, and the equivalence of the
open-subscheme bridge through `CategoryTheory.Equivalence.fullyFaithfulFunctor`, both of which are
term-level.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

universe t u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} R}

/-- **Morphisms of sheaves of modules given over the members of an open covering and agreeing on
overlaps glue to a unique global morphism**, with the index type of the covering family in an
arbitrary universe.

This is `Stacks.SheafOfModules.existsUnique_hom_of_over`, whose index type must lie in the
universe of the opens of the space, and which therefore does not apply to a covering family of the
big h category over `S` — those are indexed by a type of `Type (u + 1)`. The family is reindexed
by the opens it hits, each equipped with a choice of index realising it. -/
theorem existsUnique_hom_of_over_of_cover {ι : Type t} (V : ι → Opens (X : TopCat))
    (hV : ⨆ i, V i = ⊤) (φ : ∀ i, M.over (V i) ⟶ N.over (V i))
    (hφ : ∀ (i j : ι) (W : Opens (X : TopCat)) (hWi : W ≤ V i) (hWj : W ≤ V j),
      (φ i).val.app (op (Over.mk (homOfLE hWi))) =
        (φ j).val.app (op (Over.mk (homOfLE hWj)))) :
    ∃! ψ : M ⟶ N, ∀ i, (_root_.SheafOfModules.overFunctor R (V i)).map ψ = φ i := by
  -- the opens hit by the family, each with a choice of index realising it
  have hσ : ∀ W : { W : Opens (X : TopCat) // ∃ i, V i = W }, ∃ i, V i = W.1 := fun W => W.2
  choose σ hσeq using hσ
  have hVcov : ⨆ W : { W : Opens (X : TopCat) // ∃ i, V i = W }, V (σ W) = ⊤ := by
    rw [eq_top_iff, ← hV]
    refine iSup_le fun i => le_iSup_of_le ⟨V i, i, rfl⟩ ?_
    exact le_of_eq (hσeq ⟨V i, i, rfl⟩).symm
  obtain ⟨ψ, hψ, huniq⟩ :=
    existsUnique_hom_of_over (fun W => V (σ W)) hVcov (fun W => φ (σ W))
      fun W W' Z hZ hZ' => hφ (σ W) (σ W') Z hZ hZ'
  refine ⟨ψ, fun i => ?_, fun χ hχ => ?_⟩
  · -- at an arbitrary index, compare componentwise: the types differ by `V (σ _) = V i`
    set W : { W : Opens (X : TopCat) // ∃ i, V i = W } := ⟨V i, i, rfl⟩ with hWdef
    have hWi : V (σ W) = V i := hσeq W
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun Z => ?_)
    have hle : Z.unop.left ≤ V i := leOfHom Z.unop.hom
    have hle' : Z.unop.left ≤ V (σ W) := hle.trans (le_of_eq hWi.symm)
    have h₁ : ((_root_.SheafOfModules.overFunctor R (V (σ W))).map ψ).val.app
          (op (Over.mk (homOfLE hle'))) =
        (φ (σ W)).val.app (op (Over.mk (homOfLE hle'))) :=
      congrArg (fun θ : M.over (V (σ W)) ⟶ N.over (V (σ W)) =>
        θ.val.app (op (Over.mk (homOfLE hle')))) (hψ W)
    exact h₁.trans (hφ (σ W) i Z.unop.left hle' hle)
  · exact huniq χ fun W => hχ (σ W)

/-- **Morphisms of sheaves of modules given over the members of an open covering whose slice
restrictions to a common smaller open agree glue to a unique global morphism**, with the index
type of the covering family in an arbitrary universe.

This is `Stacks.SheafOfModules.existsUnique_hom_of_over_of_cover` with the compatibility
hypothesis as an equality of *morphisms* over the smaller open rather than of their maps on
sections.  It is the form a consumer has it in: what a morphism of descent data along a Zariski
family provides over an overlap is a morphism of sheaves of modules there, not a family of maps
on sections.

`Stacks.SheafOfModules.existsUnique_hom_of_overMap_eq_of_isBasis` is the same passage for a
covering indexed in the universe of the space and with the compatibility only over the members of
a basis; neither restriction is imposed here.  As there, the two sides of the hypothesis are
morphisms between objects that are only *definitionally* equal — the slice restriction of
`M.over (V i)` and of `M.over (V j)` to `W` are both the restriction of `M` to `W`, reindexed in
two ways — so the equation typechecks without any transport, and the passage to components is
`Stacks.SheafOfModules.overMap_map_val_app_le`. -/
theorem existsUnique_hom_of_overMap_eq_of_cover {ι : Type t} (V : ι → Opens (X : TopCat))
    (hV : ⨆ i, V i = ⊤) (φ : ∀ i, M.over (V i) ⟶ N.over (V i))
    (hφ : ∀ (i j : ι) (W : Opens (X : TopCat)) (hWi : W ≤ V i) (hWj : W ≤ V j),
      (_root_.SheafOfModules.overMap R (homOfLE hWi)).map (φ i) =
        (_root_.SheafOfModules.overMap R (homOfLE hWj)).map (φ j)) :
    ∃! ψ : M ⟶ N, ∀ i, (_root_.SheafOfModules.overFunctor R (V i)).map ψ = φ i :=
  existsUnique_hom_of_over_of_cover V hV φ fun i j W hWi hWj =>
    congrArg (fun t => t.val.app (op (Over.mk (homOfLE (le_refl W))))) (hφ i j W hWi hWj)

end Stacks.SheafOfModules

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **Morphisms of the slice restrictions `M.over V ⟶ N.over V` are the same as morphisms of the
extensions of scalars along `V.ι`.**

The transition functor of [Stacks, Tag 0EXE] along the inclusion of an open is the slice
restriction followed by the open-subscheme equivalence
(`AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback`), so the bijection is full
faithfulness of that equivalence followed by transport along the comparison at the two objects.
It is the Hom-level form in which the gluing of morphisms is read in the spelling the
pseudofunctor speaks. -/
noncomputable def frobeniusColimitPullbackHomEquivOver (V : X.Opens)
    (hV : IsInCharacteristic V.toScheme p)
    (M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) :
    (M.over V ⟶ N.over V) ≃
      ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj N) :=
  letI βM : (frobeniusColimitModuleOpenEquiv X p hX V hV).functor.obj (M.over V) ≅
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj M :=
    (frobeniusColimitModuleRestrictIsoPullback X p hX V hV).app M
  letI βN : (frobeniusColimitModuleOpenEquiv X p hX V hV).functor.obj (N.over V) ≅
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj N :=
    (frobeniusColimitModuleRestrictIsoPullback X p hX V hV).app N
  ((frobeniusColimitModuleOpenEquiv X p hX V hV).fullyFaithfulFunctor.homEquiv).trans
    (Iso.homCongr βM βN)

/-- **The bijection of `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver` carries the slice
restriction of a global morphism to its extension of scalars.**

This is naturality of `AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback` at the
morphism, and it is what lets a gluing statement about slice restrictions be read as one about
the transition functors on both sides: the hypothesis and the conclusion. -/
theorem frobeniusColimitPullbackHomEquivOver_apply_overFunctor_map (V : X.Opens)
    (hV : IsInCharacteristic V.toScheme p)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)} (φ : M ⟶ N) :
    frobeniusColimitPullbackHomEquivOver X p hX V hV M N
        ((_root_.SheafOfModules.overFunctor (frobeniusColimitRingSheaf X p hX) V).map φ) =
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p V.ι hV hX)).map φ :=
  NatIso.naturality_1 (frobeniusColimitModuleRestrictIsoPullback X p hX V hV) φ

/-- Gluing of morphisms of slice restrictions, transported along bijections `e i` that carry the
slice restriction of a global morphism to its image under `F i`. -/
private theorem existsUnique_map_eq_of_equiv {ι : Type t} (V : ι → X.Opens)
    (hVcov : ⨆ i, V i = ⊤) {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (φ : ∀ i, M.over (V i) ⟶ N.over (V i))
    (hφ : ∀ (i j : ι) (W : X.Opens) (hWi : W ≤ V i) (hWj : W ≤ V j),
      (φ i).val.app (op (Over.mk (homOfLE hWi))) =
        (φ j).val.app (op (Over.mk (homOfLE hWj))))
    {T : ι → Sort*} (e : ∀ i, (M.over (V i) ⟶ N.over (V i)) ≃ T i) (F : ∀ i, (M ⟶ N) → T i)
    (hF : ∀ i χ, e i ((_root_.SheafOfModules.overFunctor (frobeniusColimitRingSheaf X p hX)
      (V i)).map χ) = F i χ) (ψ : ∀ i, T i) (hψ : ∀ i, e i (φ i) = ψ i) :
    ∃! χ : M ⟶ N, ∀ i, F i χ = ψ i := by
  obtain ⟨χ, hχ, huniq⟩ :=
    Stacks.SheafOfModules.existsUnique_hom_of_over_of_cover
      (X := (X : TopCat)) (R := frobeniusColimitRingSheaf X p hX) (M := M) (N := N)
      (ι := ι) V hVcov φ hφ
  refine ⟨χ, fun i => ?_, fun χ' hχ' => huniq χ' fun i => (e i).injective ?_⟩
  · rw [← hF, hχ, hψ]
  · rw [hF, hχ', hψ]

/-- **Morphisms of sheaves of `colim_F 𝒪_X`-modules given over the members of an open cover of
`X` and agreeing on overlaps glue to a unique global morphism, in the transition-functor spelling
of [Stacks, Tag 0EXE].**

This is the Frobenius-colimit analogue of the gluing of morphisms of sheaves of modules
(Stacks 00AN) in the form the stack condition of
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` consumes: the full half of that condition
asks for a global morphism whose extensions of scalars along the members of the family are
prescribed, which is the existence asserted here, and its separated half — already proved as
`AlgebraicGeometry.frobeniusColimitPullback_map_injective` — is the uniqueness.

The data is given twice over, once on the slice restrictions and once on the extensions of
scalars, related by `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver`. That is not a
weakening: the comparison is a bijection, so every family `ψ` of morphisms of the extensions of
scalars arises from exactly one family `φ` of morphisms of the slice restrictions. It is how the
hypothesis is kept in the form `Stacks.SheafOfModules.existsUnique_hom_of_over_of_cover` consumes
while the conclusion stays in the form the pseudofunctor speaks — writing the hypothesis with the
inverse comparison instead makes the elaborator unfold the Frobenius colimit of the structure
sheaf in order to type the components, and it does not terminate.

The index type of the cover is arbitrary, as the families of the big h category over `S`
require. -/
theorem existsUnique_frobeniusColimitPullback_map_eq {ι : Type t} (V : ι → X.Opens)
    (hVcov : ⨆ i, V i = ⊤)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (φ : ∀ i, M.over (V i) ⟶ N.over (V i))
    (ψ : ∀ i, (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (V i).ι
          (isInCharacteristic_toScheme hX (V i)) hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (V i).ι
          (isInCharacteristic_toScheme hX (V i)) hX)).obj N)
    (hψ : ∀ i, frobeniusColimitPullbackHomEquivOver X p hX (V i)
      (isInCharacteristic_toScheme hX (V i)) M N (φ i) = ψ i)
    (hφ : ∀ (i j : ι) (W : X.Opens) (hWi : W ≤ V i) (hWj : W ≤ V j),
      (φ i).val.app (op (Over.mk (homOfLE hWi))) =
        (φ j).val.app (op (Over.mk (homOfLE hWj)))) :
    ∃! χ : M ⟶ N, ∀ i, (_root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p (V i).ι
        (isInCharacteristic_toScheme hX (V i)) hX)).map χ = ψ i := by
  exact existsUnique_map_eq_of_equiv X p hX V hVcov φ hφ
    (fun i => frobeniusColimitPullbackHomEquivOver X p hX (V i)
      (isInCharacteristic_toScheme hX (V i)) M N)
    (fun i => (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (V i).ι
      (isInCharacteristic_toScheme hX (V i)) hX)).map)
    (fun i => frobeniusColimitPullbackHomEquivOver_apply_overFunctor_map X p hX (V i)
      (isInCharacteristic_toScheme hX (V i))) ψ hψ

/-! ### Along a family of open immersions -/

/-- **The transition functor of a morphism factoring isomorphically through an open induces a
bijection on morphisms from the transition functor of that open's inclusion.**

The transition functor of the isomorphism `θ` is an equivalence
(`AlgebraicGeometry.frobeniusColimitPullbackEquivOfIso`), so it is fully faithful, and
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso` identifies its composite with the
transition of `V.ι` with the transition of `j`. -/
noncomputable def frobeniusColimitPullbackHomEquivOfFactor (V : X.Opens)
    (hV : IsInCharacteristic V.toScheme p) {Y : Scheme.{u}} (j : Y ⟶ X)
    (hY : IsInCharacteristic Y p) (θ : Y ⟶ V.toScheme) [IsIso θ] (hθ : θ ≫ V.ι = j)
    (M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) :
    ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj N) ≃
      ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p j hY hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p j hY hX)).obj N) :=
  letI τM : (frobeniusColimitPullbackEquivOfIso p (asIso θ) hY hV).functor.obj
        ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj M) ≅
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p j hY hX)).obj M :=
    (frobeniusColimitPullbackTriangleIso p θ V.ι j hY hV hX hθ).app M
  letI τN : (frobeniusColimitPullbackEquivOfIso p (asIso θ) hY hV).functor.obj
        ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj N) ≅
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p j hY hX)).obj N :=
    (frobeniusColimitPullbackTriangleIso p θ V.ι j hY hV hX hθ).app N
  ((frobeniusColimitPullbackEquivOfIso p (asIso θ) hY hV).fullyFaithfulFunctor.homEquiv).trans
    (Iso.homCongr τM τN)

/-- The bijection of `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOfFactor` carries the
extension of scalars of a global morphism along `V.ι` to its extension of scalars along `j`.
This is naturality of `AlgebraicGeometry.frobeniusColimitPullbackTriangleIso`. -/
theorem frobeniusColimitPullbackHomEquivOfFactor_apply_map (V : X.Opens)
    (hV : IsInCharacteristic V.toScheme p) {Y : Scheme.{u}} (j : Y ⟶ X)
    (hY : IsInCharacteristic Y p) (θ : Y ⟶ V.toScheme) [IsIso θ] (hθ : θ ≫ V.ι = j)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)} (χ : M ⟶ N) :
    frobeniusColimitPullbackHomEquivOfFactor X p hX V hV j hY θ hθ M N
        ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p V.ι hV hX)).map χ) =
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p j hY hX)).map χ :=
  NatIso.naturality_1 (frobeniusColimitPullbackTriangleIso p θ V.ι j hY hV hX hθ) χ

/-- **Morphisms of the slice restriction of `M` to the image of an open immersion `g` are the same
as morphisms of the extensions of scalars along `g`.**

This is `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOver` at the image of `g`, followed by
`AlgebraicGeometry.frobeniusColimitPullbackHomEquivOfFactor` at the canonical factorisation of `g`
through that image. It is the form in which the full half of the stack condition for
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` reads its data: the components of a
morphism of descent data along a family `g i : Y i ⟶ X` live over the `Y i`, not over opens
of `X`. -/
noncomputable def frobeniusColimitPullbackHomEquivOpenImmersion {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g] (hY : IsInCharacteristic Y p)
    (M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) :
    (M.over g.opensRange ⟶ N.over g.opensRange) ≃
      ((_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p g hY hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p g hY hX)).obj N) :=
  (frobeniusColimitPullbackHomEquivOver X p hX g.opensRange
      (isInCharacteristic_toScheme hX g.opensRange) M N).trans
    (frobeniusColimitPullbackHomEquivOfFactor X p hX g.opensRange
      (isInCharacteristic_toScheme hX g.opensRange) g hY
      (IsOpenImmersion.isoOfRangeEq g g.opensRange.ι (by simp)).hom
      (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _) M N)

/-- The bijection of `AlgebraicGeometry.frobeniusColimitPullbackHomEquivOpenImmersion` carries the
slice restriction of a global morphism to its extension of scalars along `g`. -/
theorem frobeniusColimitPullbackHomEquivOpenImmersion_apply_overFunctor_map {Y : Scheme.{u}}
    (g : Y ⟶ X) [IsOpenImmersion g] (hY : IsInCharacteristic Y p)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)} (χ : M ⟶ N) :
    frobeniusColimitPullbackHomEquivOpenImmersion X p hX g hY M N
        ((_root_.SheafOfModules.overFunctor (frobeniusColimitRingSheaf X p hX)
          g.opensRange).map χ) =
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p g hY hX)).map χ :=
  (congrArg
      (frobeniusColimitPullbackHomEquivOfFactor X p hX g.opensRange
        (isInCharacteristic_toScheme hX g.opensRange) g hY
        (IsOpenImmersion.isoOfRangeEq g g.opensRange.ι (by simp)).hom
        (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _) M N)
      (frobeniusColimitPullbackHomEquivOver_apply_overFunctor_map X p hX g.opensRange
        (isInCharacteristic_toScheme hX g.opensRange) χ)).trans
    (frobeniusColimitPullbackHomEquivOfFactor_apply_map X p hX g.opensRange
      (isInCharacteristic_toScheme hX g.opensRange) g hY
      (IsOpenImmersion.isoOfRangeEq g g.opensRange.ι (by simp)).hom
      (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _) χ)

/-- **Morphisms of sheaves of `colim_F 𝒪_X`-modules given over the members of a family of open
immersions whose images cover `X`, in the transition-functor spelling of [Stacks, Tag 0EXE], and
agreeing on overlaps, glue to a unique global morphism.**

This is the form the full half of the stack condition for
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` at a Zariski family of the big h category
over `S` consumes: a morphism of descent data along such a family has one component over each
member, and what has to be produced is a global morphism whose extensions of scalars are those
components. The uniqueness is the separated half, already proved as
`AlgebraicGeometry.frobeniusColimitPullback_map_injective_of_openImmersion`; what is added is the
existence.

The members of the family need not be inclusions of opens — the family a Zariski presieve of the
big h category over `S` presents is a family of open immersions of schemes — and the index type
is arbitrary. -/
theorem existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion {ι : Type t}
    {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hY : ∀ i, IsInCharacteristic (Y i) p) (hcov : ⨆ i, (g i).opensRange = ⊤)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (φ : ∀ i, M.over (g i).opensRange ⟶ N.over (g i).opensRange)
    (ψ : ∀ i, (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).obj N)
    (hψ : ∀ i, frobeniusColimitPullbackHomEquivOpenImmersion X p hX (g i) (hY i) M N (φ i) = ψ i)
    (hφ : ∀ (i₁ i₂ : ι) (W : X.Opens) (hW₁ : W ≤ (g i₁).opensRange)
        (hW₂ : W ≤ (g i₂).opensRange),
      (φ i₁).val.app (op (Over.mk (homOfLE hW₁))) =
        (φ i₂).val.app (op (Over.mk (homOfLE hW₂)))) :
    ∃! χ : M ⟶ N, ∀ i, (_root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).map χ = ψ i := by
  exact existsUnique_map_eq_of_equiv X p hX (fun i => (g i).opensRange) hcov φ hφ
    (fun i => frobeniusColimitPullbackHomEquivOpenImmersion X p hX (g i) (hY i) M N)
    (fun i => (_root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).map)
    (fun i => frobeniusColimitPullbackHomEquivOpenImmersion_apply_overFunctor_map X p hX (g i)
      (hY i)) ψ hψ

/-- **Morphisms of sheaves of `colim_F 𝒪_X`-modules given over the members of a family of open
immersions whose images cover `X`, in the transition-functor spelling of [Stacks, Tag 0EXE], and
whose slice restrictions to a common smaller open agree, glue to a unique global morphism.**

This is `AlgebraicGeometry.existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion` with the
overlap hypothesis as an equality of *morphisms* over the smaller open instead of an equality of
their maps on sections, by
`Stacks.SheafOfModules.existsUnique_hom_of_overMap_eq_of_cover`.

It is the shape the full half of the stack condition for
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor` at a Zariski family of the big h category
over `S` will consume: the compatibility a morphism of descent data carries over an object of the
site mapping to two members of the family is an equality of morphisms of sheaves of modules
there, not of maps on sections, so the component form had to be crossed before the hypothesis
could be matched. -/
theorem existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion_of_overMap {ι : Type t}
    {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hY : ∀ i, IsInCharacteristic (Y i) p) (hcov : ⨆ i, (g i).opensRange = ⊤)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (φ : ∀ i, M.over (g i).opensRange ⟶ N.over (g i).opensRange)
    (ψ : ∀ i, (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).obj N)
    (hψ : ∀ i, frobeniusColimitPullbackHomEquivOpenImmersion X p hX (g i) (hY i) M N (φ i) = ψ i)
    (hφ : ∀ (i₁ i₂ : ι) (W : X.Opens) (hW₁ : W ≤ (g i₁).opensRange)
        (hW₂ : W ≤ (g i₂).opensRange),
      (_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX)
          (homOfLE hW₁)).map (φ i₁) =
        (_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX)
          (homOfLE hW₂)).map (φ i₂)) :
    ∃! χ : M ⟶ N, ∀ i, (_root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).map χ = ψ i :=
  existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion X p hX g hY hcov φ ψ hψ
    fun i₁ i₂ W hW₁ hW₂ =>
      congrArg (fun t => t.val.app (op (Over.mk (homOfLE (le_refl W)))))
        (hφ i₁ i₂ W hW₁ hW₂)

/-- **The same along a family of open immersions whose images cover `X`, with the compatibility
available only over the members of a prescribed basis.**

This is
`AlgebraicGeometry.existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion_of_overMap` with
its compatibility hypothesis weakened from *every* open below two members of the covering to the
members of a basis below two members; the two are equivalent by
`Stacks.SheafOfModules.overMap_map_eq_of_isBasis`, since both slice restrictions commute with
passing to a smaller open and the target is a sheaf.

It is the shape the final Zariski glueing of [Stacks, Tag 0EXD] consumes:  there the covering of
`Spec A` is by basic opens and the local data are compared over a basic open below two members,
because only over a basic open is the almost blowup square of [Stacks, Example 0EVH] again a
two-generator square, namely the one over the localisation.  Over an arbitrary open below two
members there is no local square at all, and so no local comparison to appeal to. -/
theorem existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion_of_isBasis {ι : Type t}
    {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hY : ∀ i, IsInCharacteristic (Y i) p) (hcov : ⨆ i, (g i).opensRange = ⊤)
    {B : Set X.Opens} (hB : Opens.IsBasis B)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)}
    (φ : ∀ i, M.over (g i).opensRange ⟶ N.over (g i).opensRange)
    (ψ : ∀ i, (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u}
          (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).obj N)
    (hψ : ∀ i, frobeniusColimitPullbackHomEquivOpenImmersion X p hX (g i) (hY i) M N (φ i) = ψ i)
    (hφ : ∀ (i₁ i₂ : ι), ∀ W ∈ B, ∀ (hW₁ : W ≤ (g i₁).opensRange)
        (hW₂ : W ≤ (g i₂).opensRange),
      (_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX)
          (homOfLE hW₁)).map (φ i₁) =
        (_root_.SheafOfModules.overMap (frobeniusColimitRingSheaf X p hX)
          (homOfLE hW₂)).map (φ i₂)) :
    ∃! χ : M ⟶ N, ∀ i, (_root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p (g i) (hY i) hX)).map χ = ψ i :=
  existsUnique_frobeniusColimitPullback_map_eq_of_openImmersion_of_overMap X p hX g hY hcov φ ψ hψ
    fun i₁ i₂ _W hW₁ hW₂ =>
      Stacks.SheafOfModules.overMap_map_eq_of_isBasis hB (φ i₁) (φ i₂)
        (fun W' hW'B => hφ i₁ i₂ W' hW'B) hW₁ hW₂

end AlgebraicGeometry

end
