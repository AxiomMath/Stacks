module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctoriality

/-!
# The fundamental triangle of the cotangent complex of sheaves of rings

Let `C` be a site and let `A ⟶ B ⟶ D` be homomorphisms of sheaves of commutative rings on `C`
(the source writes the site `𝒟` and the tower `𝒜 → ℬ → 𝒞`; here `C` already names the site, so
the third sheaf of rings is called `D`). The tower produces two commutative squares of
homomorphisms, over the identity of `A` and over the identity of `D` respectively, so the square
functoriality of the cotangent complex of
`StacksFrontier.Cotangent.SheavesOfRings.SquareFunctoriality` produces the two displayed arrows of
the triangle of Tag 08SZ:

* the change-of-base-ring map `L_{D/A} ⟶ L_{D/B}`, directly; and
* the `B`-linear map `L_{B/A} ⟶ L_{D/A}`, whose transpose along the extension–restriction
  adjunction for sheaves of modules is the map `L_{B/A} ⊗_B D ⟶ L_{D/A}` out of the
  base-changed cotangent complex.

## Main definitions

* `CategoryTheory.Sheaf.towerExtendScalars` is extension of scalars `- ⊗_B D` along `h : B ⟶ D`
  for sheaves of modules on the site, and `CategoryTheory.Sheaf.towerExtendRestrictAdjunction`
  its adjunction with restriction of scalars.
* `CategoryTheory.Sheaf.towerBaseChangeSquare` and
  `CategoryTheory.Sheaf.towerFunctorialitySquare` are the two maps of standard resolutions
  attached to the two squares of the tower.
* `CategoryTheory.Sheaf.baseChangedCotangentSimplicialModule` and
  `CategoryTheory.Sheaf.baseChangedCotangentComplex` are the degreewise base change
  `(Ω_{P_•/A} ⊗_{P_•} B) ⊗_B D` of the cotangent simplicial module of `A ⟶ B` and its
  associated cochain complex: the first vertex of the triangle, with the **degreewise** tensor
  product in place of the derived one.
* `CategoryTheory.Sheaf.baseChangeSimplicialMap` is the degreewise transpose of the map of
  base-changed sheaves of differentials attached to the first square.
* `CategoryTheory.Sheaf.towerCotangentBaseChange` is **the first displayed arrow**
  `L_{B/A} ⊗_B D ⟶ L_{D/A}`, and `CategoryTheory.Sheaf.towerCotangentChangeOfBase` is **the
  second displayed arrow** `L_{D/A} ⟶ L_{D/B}`.

## Main results

* `CategoryTheory.Sheaf.baseChangeSimplicialMap_transpose`: the degreewise map of the first
  arrow is the transpose of the canonical map of base-changed sheaves of differentials, so it is
  pinned by the universal property of the base change.
* `CategoryTheory.Sheaf.baseChangeSimplicialMap_derivation` and
  `CategoryTheory.Sheaf.towerCotangentChangeOfBase_derivation`: in each simplicial degree the
  two arrows carry the universal derivation of the degree-`n` term of one standard resolution to
  the universal derivation of the corresponding term of the other, precomposed with the map of
  standard resolutions. These are the sheaf-level forms of `1 ⊗ d p ↦ 1 ⊗ d p` which say that
  the two arrows are the canonical ones.
* `CategoryTheory.Sheaf.towerCotangentBaseChange_f`: in cohomological degree `-n` the first
  arrow is the degreewise transpose, read through the canonical degree isomorphisms.
* `CategoryTheory.Sheaf.exists_distTriang_cotangentComplexDerived_of_shortExact`: **Tag 08SZ**
  under one carried hypothesis — granted the sheaf-level differential short exact sequence, the
  triangle on the three named vertices, *with the two displayed arrows being exactly the two
  canonical maps constructed here*, is distinguished in `D(D)`.

## What is proved and what is not

Tag 08SZ asserts the existence of a canonical distinguished triangle

`L_{B/A} ⊗^𝐋_B D ⟶ L_{D/A} ⟶ L_{D/B} ⟶ (L_{B/A} ⊗^𝐋_B D)[1]`

in `D(D)`. The two displayed arrows are constructed here, unconditionally and canonically: they
are the square-functoriality maps of the two squares of the tower, characterized by their effect
on universal derivations. **Distinguishedness is not proved unconditionally**; it is carried, by
one named hypothesis, in
`CategoryTheory.Sheaf.exists_distTriang_cotangentComplexDerived_of_shortExact`.

### The carried hypothesis

The source's proof constructs, for `B ⟶ D` injective, a short exact sequence of simplicial
`D`-modules out of `Ω_{P_•/A}`, `Ω_{Q_•/A}` and `Ω_{Q̄_•/B}` — where `P_•` resolves `B` over `A`,
`Q_•` resolves `D` over `A` and `Q̄_• = Q_• ⊗_{P_•} B` — each tensored down to `D`; this is the
construction of Tag 08SD, carried out on presheaves and then sheafified, so that its exactness
reduces to the ring-level statement for the sections `A(U) → B(U) → D(U)`. Identifying its third
term with `L_{D/B}` needs the two quasi-isomorphisms of the source's proof, resting on Tag 08SE,
and the general case is reduced to the injective one by replacing `D` with `B × D`, which needs
the isomorphism of Tag 08SY.

The short exact sequence itself is taken as the hypothesis, in the shape the source produces
it: a short complex `S` of cochain complexes of sheaves of `D`-modules, short exact, whose three
terms are identified with the three vertices and whose two maps are the two canonical arrows
constructed here. That is the input of the source's argument, not its conclusion: a short exact
sequence of complexes is strictly more specific data than a distinguished triangle on its
vertices, and the passage from one to the other —
`DerivedCategory.triangleOfSES_distinguished` — is the content that is proved
here. The hypotheses `hf` and `hg` are what make the conclusion a statement about the
*canonical* triangle rather than about some triangle on the same three objects.

### The first vertex is the degreewise, not the derived, tensor product

`CategoryTheory.Sheaf.baseChangedCotangentComplex` is the complex of the degreewise base change
`(Ω_{P_n/A} ⊗_{P_n} B) ⊗_B D`, not `L_{B/A} ⊗^𝐋_B D`. The two agree because each term of
`L_{B/A}` is, locally, a free `B`-module, which is not proved here.

## Implementation notes

The two squares are `(𝟙 A, h)` from `g` to `g ≫ h` and `(g, 𝟙 D)` from `g ≫ h` to `h`. In the
second one the right-hand edge is the identity of `D`, and restriction of scalars along the
identity is the identity functor by reflexivity, so
`CategoryTheory.Sheaf.towerCotangentChangeOfBase` has the two cotangent complexes themselves as
source and target, with no restriction wrapper: that is why the second arrow needs no
identification at all.

The first arrow is assembled degreewise. Transposing the degreewise map
`Ω_{P_n/A} ⊗_{P_n} B ⟶ Ω_{Q_n/A} ⊗_{Q_n} D` of
`CategoryTheory.Sheaf.squareCotangentTermMap` along
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction` gives a `D`-linear map out
of the base change in each degree; the two naturality lemmas of the adjunction turn the
simplicial naturality of the former into the simplicial naturality of the latter, and the
alternating-face-map complex and `HomologicalComplex.extendMap` then give the map of cochain
complexes without any further comparison isomorphism.

The site-object and site-morphism universes are independent of the universe of sections, as in
`CategoryTheory.Sheaf.cotangentComplex`; the three sheaves of rings share the sections universe,
the tower being over one site.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ), the triangle.
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex
  of a homomorphism of sheaves of rings.
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR), the standard
  resolution.
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD), the differential
  sequence the carried hypothesis stands for.
* [Stacks Project, Tag 08SE](https://stacks.math.columbia.edu/tag/08SE), the identification of
  the third vertex.
* [Stacks Project, Tag 08SY](https://stacks.math.columbia.edu/tag/08SY), the reduction to the
  injective case.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension of scalars
  for sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicTopology Opposite Simplicial
open Stacks.Sheaves.RingedToposModules (extendScalars extendRestrictScalarsAdjunction)

universe u v w t

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-! ## Extension of scalars along the upper homomorphism of the tower -/

/-- Extension of scalars `- ⊗_B D` along `h : B ⟶ D` for sheaves of modules on the site: the
sectionwise tensor product, sheafified. This is the functor of Tag 03CZ. -/
noncomputable abbrev towerExtendScalars :
    targetModules.{u, v, w} J B ⥤ targetModules.{u, v, w} J D :=
  extendScalars J h.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).property
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).property

/-- Extension of scalars along `h : B ⟶ D` is left adjoint to restriction of scalars along `h`,
the functor `CategoryTheory.Sheaf.squareRestrict` of the square functoriality. -/
noncomputable abbrev towerExtendRestrictAdjunction :
    towerExtendScalars.{u, v, w} J h ⊣ squareRestrict.{u, v, w} J h :=
  extendRestrictScalarsAdjunction J h.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).property
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} D).property

/-! ## The two squares of the tower -/

/-- The map of standard resolutions attached to the square `(𝟙 A, h)` from `g : A ⟶ B` to
`g ≫ h : A ⟶ D`: the square over the identity of the base sheaf of rings whose right-hand edge
is the upper homomorphism of the tower. -/
noncomputable abbrev towerBaseChangeSquare :
    ResolutionSquareMap.{u, v, w} J g (g ≫ h) (𝟙 A) h :=
  resolutionSquareMap.{u, v, w} J (𝟙 A) h (by simp)

/-- The map of standard resolutions attached to the square `(g, 𝟙 D)` from `g ≫ h : A ⟶ D` to
`h : B ⟶ D`: the square over the identity of the total sheaf of rings whose left-hand edge is
the lower homomorphism of the tower. -/
noncomputable abbrev towerFunctorialitySquare :
    ResolutionSquareMap.{u, v, w} J (g ≫ h) h g (𝟙 D) :=
  resolutionSquareMap.{u, v, w} J g (𝟙 D) (by simp)

/-! ## The base-changed cotangent complex: the first vertex -/

/-- The degreewise base change `(Ω_{P_•/A} ⊗_{P_•} B) ⊗_B D` of the cotangent simplicial module
of `A ⟶ B`: a simplicial sheaf of `D`-modules. -/
noncomputable abbrev baseChangedCotangentSimplicialModule :
    SimplicialObject (targetModules.{u, v, w} J D) :=
  ((SimplicialObject.whiskering _ _).obj (towerExtendScalars.{u, v, w} J h)).obj
    (cotangentSimplicialModule.{u, v, w} J g).object

/-- The complex `L_{B/A} ⊗_B D` of the first vertex of the triangle of Tag 08SZ: the
alternating-face-map complex of the degreewise base change, reindexed so that simplicial degree
`n` lies in cohomological degree `-n`. The tensor product is the degreewise one, not the derived
one; see the module documentation. -/
noncomputable def baseChangedCotangentComplex :
    CochainComplex (targetModules.{u, v, w} J D) ℤ :=
  ((alternatingFaceMapComplex (targetModules.{u, v, w} J D)).obj
      (baseChangedCotangentSimplicialModule.{u, v, w} J g h)).extend
    (ComplexShape.embeddingUpIntLE 0)

/-- The term of the first vertex in cohomological degree `-n` is the base change of the
degree-`n` term of the cotangent simplicial module of `A ⟶ B`. -/
noncomputable def baseChangedCotangentComplex_degreeIso (n : ℕ) :
    (baseChangedCotangentComplex.{u, v, w} J g h).X (-(n : ℤ)) ≅
      (towerExtendScalars.{u, v, w} J h).obj
        ((cotangentSimplicialModule.{u, v, w} J g).object.obj (op ⦋n⦌)) :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE 0) (by simp)

/-! ## The two displayed arrows -/

/-- The map of simplicial sheaves of `D`-modules `(Ω_{P_•/A} ⊗_{P_•} B) ⊗_B D ⟶ Ω_{Q_•/A} ⊗_{Q_•}
D` obtained by transposing, in each simplicial degree, the map of base-changed sheaves of
differentials attached to the square `(𝟙 A, h)`. -/
noncomputable def baseChangeSimplicialMap :
    baseChangedCotangentSimplicialModule.{u, v, w} J g h ⟶
      (cotangentSimplicialModule.{u, v, w} J (g ≫ h)).object where
  app n := ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm
    (squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g h) n)
  naturality _ _ m := by
    have h₁ := congrArg
      (fun k => ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm k)
      (squareCotangentTermMap_naturality (towerBaseChangeSquare.{u, v, w} J g h) m)
    rw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_right_symm] at h₁
    exact h₁

/-- The degreewise map of the first arrow is the transpose of the canonical map of base-changed
sheaves of differentials. -/
lemma baseChangeSimplicialMap_app (n : SimplexCategoryᵒᵖ) :
    (baseChangeSimplicialMap.{u, v, w} J g h).app n =
      ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm
        (squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g h) n) :=
  rfl

/-- The degreewise map of the first arrow is the transpose of the canonical map of base-changed
sheaves of differentials: composing it with the unit `x ↦ 1 ⊗ x` of the extension–restriction
adjunction returns `CategoryTheory.Sheaf.squareCotangentTermMap`. Since the transpose is a
bijection this characterizes the degreewise map. -/
lemma baseChangeSimplicialMap_transpose (n : SimplexCategoryᵒᵖ) :
    (towerExtendRestrictAdjunction.{u, v, w} J h).unit.app
          ((cotangentSimplicialModule.{u, v, w} J g).object.obj n) ≫
        (squareRestrict.{u, v, w} J h).map
          ((baseChangeSimplicialMap.{u, v, w} J g h).app n) =
      squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g h) n := by
  have h₀ : ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _)
        ((baseChangeSimplicialMap.{u, v, w} J g h).app n) =
      squareCotangentTermMap (towerBaseChangeSquare.{u, v, w} J g h) n :=
    ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).apply_symm_apply _
  rw [Adjunction.homEquiv_unit] at h₀
  exact h₀

/-- **The first arrow is the canonical one.** In each simplicial degree the transpose of the
degreewise map of the first arrow carries the universal `A`-derivation of `P_n` to the universal
`A`-derivation of `Q_n` precomposed with the map `P_n ⟶ Q_n` of standard resolutions: the
sheaf-level form of `1 ⊗ d p ↦ 1 ⊗ d p`. -/
lemma baseChangeSimplicialMap_derivation (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J g n).obj.obj U) :
    ((cotangentSimplicialModule.{u, v, w} J g).derivationEquiv n _
        ((towerExtendRestrictAdjunction.{u, v, w} J h).unit.app
            ((cotangentSimplicialModule.{u, v, w} J g).object.obj n) ≫
          (squareRestrict.{u, v, w} J h).map
            ((baseChangeSimplicialMap.{u, v, w} J g h).app n))).d x =
      ((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).universalDerivation n).d
        (((towerBaseChangeSquare.{u, v, w} J g h).resolution n).hom.app U x) := by
  rw [baseChangeSimplicialMap_transpose]
  exact squareCotangentTermMap_d (towerBaseChangeSquare.{u, v, w} J g h) n U x

/-- **Stacks Project, Tag 08SZ, the first displayed arrow.** The canonical map
`L_{B/A} ⊗_B D ⟶ L_{D/A}` of complexes of sheaves of `D`-modules: the transpose, along the
extension–restriction adjunction for sheaves of modules, of the `B`-linear map of cotangent
complexes attached to the square `(𝟙 A, h)` of the tower.

The tensor product in the source is the degreewise one, not the derived one; see the module
documentation. -/
@[stacks 08SZ "the first displayed arrow L_{B/A} ⊗_B C ⟶ L_{C/A}, with the DEGREEWISE tensor \
  product in place of the derived one — the two agree only once the terms of L_{B/A} are known \
  to be locally free, which is not proved here and for which no derived extension of scalars \
  for sheaves of modules on a site exists in this library. Distinguishedness of the triangle is \
  not claimed by this declaration"]
noncomputable def towerCotangentBaseChange :
    baseChangedCotangentComplex.{u, v, w} J g h ⟶ cotangentComplex.{u, v, w} J (g ≫ h) :=
  HomologicalComplex.extendMap
    ((alternatingFaceMapComplex (targetModules.{u, v, w} J D)).map
      (baseChangeSimplicialMap.{u, v, w} J g h))
    (ComplexShape.embeddingUpIntLE 0)

/-- In cohomological degree `-n` the first arrow is the degreewise transpose, read through the
two canonical degree isomorphisms. -/
lemma towerCotangentBaseChange_f (n : ℕ) :
    (towerCotangentBaseChange.{u, v, w} J g h).f (-(n : ℤ)) =
      (baseChangedCotangentComplex_degreeIso.{u, v, w} J g h n).hom ≫
        (baseChangeSimplicialMap.{u, v, w} J g h).app (op ⦋n⦌) ≫
          (cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) n).inv := by
  have hn : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  rw [towerCotangentBaseChange, HomologicalComplex.extendMap_f _ _ hn]
  rfl

/-- **Stacks Project, Tag 08SZ, the second displayed arrow.** The canonical
change-of-base-ring map `L_{D/A} ⟶ L_{D/B}` of complexes of sheaves of `D`-modules: the map of
cotangent complexes attached to the square `(g, 𝟙 D)` of the tower. Restriction of scalars along
the identity of `D` is the identity functor, so no identification intervenes between the stated
target and `L_{D/B}`. -/
@[stacks 08SZ "the second displayed arrow L_{C/A} ⟶ L_{C/B}, unconditionally and with no \
  identification intervening. Distinguishedness of the triangle is not claimed by this \
  declaration"]
noncomputable def towerCotangentChangeOfBase :
    cotangentComplex.{u, v, w} J (g ≫ h) ⟶ cotangentComplex.{u, v, w} J h :=
  squareCotangentComplexMap (towerFunctorialitySquare.{u, v, w} J g h)

/-- **The second arrow is the canonical one.** In cohomological degree `-n` it carries the
universal `A`-derivation of `Q_n`, the degree-`n` term of the standard resolution of `A ⟶ D`, to
the universal `B`-derivation of the degree-`n` term of the standard resolution of `B ⟶ D`
precomposed with the map of standard resolutions: the sheaf-level form of
`1 ⊗ d q ↦ 1 ⊗ d q`. -/
lemma towerCotangentChangeOfBase_derivation (n : ℕ) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J (g ≫ h) (op ⦋n⦌)).obj.obj U) :
    ((cotangentSimplicialModule.{u, v, w} J (g ≫ h)).derivationEquiv (op ⦋n⦌) _
        ((cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) n).inv ≫
          (towerCotangentChangeOfBase.{u, v, w} J g h).f (-(n : ℤ)) ≫
            (cotangentComplex_degreeIso.{u, v, w} J h n).hom)).d x =
      ((cotangentSimplicialModule.{u, v, w} J h).universalDerivation (op ⦋n⦌)).d
        (((towerFunctorialitySquare.{u, v, w} J g h).resolution (op ⦋n⦌)).hom.app U x) :=
  squareCotangentComplexMap_derivation (towerFunctorialitySquare.{u, v, w} J g h) n U x

/-! ## The distinguished triangle -/

/-- Three isomorphisms onto the objects of a distinguished triangle, together with the
identification of its first two morphisms with two given ones, produce a distinguished triangle
whose first two morphisms are exactly those two. -/
private lemma exists_distTriang_of_arrows {E : Type*} [Category E] [Preadditive E]
    [HasZeroObject E] [HasShift E ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor E n).Additive]
    [Pretriangulated E] {X Y Z : E} (T : Triangle E) (hT : T ∈ distTriang E)
    (d₁ : T.obj₁ ≅ X) (d₂ : T.obj₂ ≅ Y) (d₃ : T.obj₃ ≅ Z) (α : X ⟶ Y) (β : Y ⟶ Z)
    (hα : T.mor₁ = d₁.hom ≫ α ≫ d₂.inv) (hβ : T.mor₂ = d₂.hom ≫ β ≫ d₃.inv) :
    ∃ δ : Z ⟶ X⟦(1 : ℤ)⟧, Triangle.mk α β δ ∈ distTriang E := by
  refine ⟨d₃.inv ≫ T.mor₃ ≫ d₁.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ d₁.symm d₂.symm d₃.symm ?_ ?_ ?_)⟩
  · simp [hα]
  · simp [hβ]
  · simp

/-- **Stacks Project, Tag 08SZ, under one carried hypothesis.** Let `A ⟶ B ⟶ D` be homomorphisms
of sheaves of commutative rings on a site. Then there is a distinguished triangle

`L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/B} ⟶ (L_{B/A} ⊗_B D)[1]`

in `D(D)` whose first two arrows are the two canonical maps
`CategoryTheory.Sheaf.towerCotangentBaseChange` and
`CategoryTheory.Sheaf.towerCotangentChangeOfBase` constructed above.

The hypothesis carried is the sheaf-level differential short exact sequence of the source's
proof (Tag 08SD): a short complex `S` of cochain complexes of sheaves of `D`-modules that is
short exact (`hS`), whose three terms are the three vertices (`e₁`, `e₂`, `e₃`) and whose two
maps are the two canonical arrows (`hf`, `hg`). The source identifies the third term using
Tag 08SE and reduces to the case of an injective `B ⟶ D` using the isomorphism of Tag 08SY.

The first vertex carries the degreewise, not the derived, tensor product; see the module
documentation. -/
@[stacks 08SZ "the distinguished triangle, under ONE carried hypothesis the source lacks: the \
  short exact sequence `S`, `hS` realizing the two canonical arrows (`hf`, `hg`) on the three \
  vertices (`e₁`, `e₂`, `e₃`) — the sheaf-level analogue of Tag 08SD, absent from this library, \
  as are Tag 08SE and the ISOMORPHISM of Tag 08SY. The first vertex carries the DEGREEWISE \
  tensor product in place of the derived one"]
theorem exists_distTriang_cotangentComplexDerived_of_shortExact
    [HasDerivedCategory.{t} (targetModules.{u, v, w} J D)]
    (S : ShortComplex (CochainComplex (targetModules.{u, v, w} J D) ℤ)) (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ baseChangedCotangentComplex.{u, v, w} J g h)
    (e₂ : S.X₂ ≅ cotangentComplex.{u, v, w} J (g ≫ h))
    (e₃ : S.X₃ ≅ cotangentComplex.{u, v, w} J h)
    (hf : S.f = e₁.hom ≫ towerCotangentBaseChange.{u, v, w} J g h ≫ e₂.inv)
    (hg : S.g = e₂.hom ≫ towerCotangentChangeOfBase.{u, v, w} J g h ≫ e₃.inv) :
    ∃ δ : cotangentComplexDerived.{u, v, w, t} J h ⟶
        (DerivedCategory.Q.obj (baseChangedCotangentComplex.{u, v, w} J g h))⟦(1 : ℤ)⟧,
      Triangle.mk (DerivedCategory.Q.map (towerCotangentBaseChange.{u, v, w} J g h))
          (DerivedCategory.Q.map (towerCotangentChangeOfBase.{u, v, w} J g h)) δ ∈
        distTriang (DerivedCategory (targetModules.{u, v, w} J D)) := by
  refine exists_distTriang_of_arrows _ (DerivedCategory.triangleOfSES_distinguished hS)
    (DerivedCategory.Q.mapIso e₁) (DerivedCategory.Q.mapIso e₂) (DerivedCategory.Q.mapIso e₃)
    _ _ ?_ ?_
  · change DerivedCategory.Q.map S.f = _
    simp [hf]; rfl
  · change DerivedCategory.Q.map S.g = _
    simp [hg]; rfl

end CategoryTheory.Sheaf

end
