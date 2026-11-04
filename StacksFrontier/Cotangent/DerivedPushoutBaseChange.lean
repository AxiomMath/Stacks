module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import StacksFrontier.Cotangent.BaseChangeQuasiIsoUnconditional
public import StacksFrontier.Cotangent.DerivedBaseChange
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteBaseChangeDifferentials
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteModuleShriekDerived
public import StacksFrontier.Cotangent.PolynomialSiteBaseChangeShriek
public import StacksFrontier.Cotangent.ResolutionCotangentDerived
public import StacksFrontier.RingTheory.Tor.TorOneBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of the cotangent complex along a derived pushout square

Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings which induces a quasi-isomorphism `B ⊗_A^𝐋 A' = B'`.
**[Stacks, Tag 08QQ]** asserts that then *the functoriality map* induces an isomorphism

`L_{B/A} ⊗^𝐋_B B' ⟶ L_{B'/A'}`

in `D(B')`. This file proves that, as
`CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso` together with
`CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso_hom`, which pins the underlying
morphism to the functoriality map of [Stacks, Tag 08PN]. It also proves the weaker identification
of the two objects alone by an independent, site-theoretic route,
`CommAlgCat.derivedCotangentComplexBaseChangeIso`; that one does not carry the tag.

## The proof

The source's proof runs through the site `C_{B/A}` of polynomial `A`-algebras augmented to `B` of
[Stacks, Tag 08PR] and its base change of [Stacks, Tag 08QN], and uses three inputs: the
identification `L_{B/A} = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` of [Stacks, Tag 08PU], the commutation of
`Lπ_!` with a change of coefficient rings of [Stacks, Tag 08Q8], and the invariance of `Lπ_!`
under the base change of the sites of [Stacks, Tag 08QP]. The route taken here replaces the last
two by the *resolution* that both of them are proved through, which shortens the argument
considerably:

* the cotangent complex is a bounded above complex of free `B`-modules
  (`CommAlgCat.projective_cotangentComplex_X'`), so `L_{B/A} ⊗^𝐋_B B'` is the degreewise base
  change `B' ⊗_B L_{B/A}` (`CommAlgCat.derivedExtensionScalarsCotangentComplexIso`). This is
  where the source's appeal to [Stacks, Tag 08Q8] is spent;
* degreewise, `B' ⊗_B (B ⊗_{P} Ω[P⁄A]) = B' ⊗_{P'} Ω[P'⁄A']` for `P' = A' ⊗_A P`, by the
  base-change isomorphism `Ω[P'⁄A'] = P' ⊗_P Ω[P⁄A]` of Kähler differentials. This is the "direct
  inspection" of the source, and it is `CommAlgCat.overDifferentialsBaseChangeNatIso` of
  `StacksFrontier.Cotangent.BaseChangeQuasiIso`, stated there for all augmented algebras at once so
  that it may be whiskered onto a resolution;
* so `B' ⊗_B L_{B/A}` is the extended Moore complex of `i^*Ω_{𝒪'/A'}` evaluated on the image of
  the standard resolution of `B` over `A` under the base-change functor of the sites. The
  hypothesis makes that image a resolution of `B'` over `A'`
  (`CommAlgCat.isResolution_augmentationBaseChange`) and hence a point resolution of `C_{B'/A'}`
  (`CommAlgCat.isPointResolution_smallPolynomialBaseChange`) — which is exactly the content of
  [Stacks, Tag 08QP] — so the derived form of [Stacks, Tag 08PT]
  (`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`) computes
  `Lπ'_!(Ω_{𝒪'/A'} ⊗_{𝒪'} B̲')` by it;
* and [Stacks, Tag 08PU] in `D(B')` identifies the latter with `L_{B'/A'}`.

## Main definitions

* `ComplexShape.Embedding.extendMapIso`: an additive functor commutes with the extension of a
  complex along an embedding of complex shapes.

## Main results

* `CommAlgCat.derivedCotangentComplexBaseChangeIso` is proved from [Stacks, Tag 08PU] in `D(B)`
  for an arbitrary resolution, `CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso`, and
  its companion for the standard resolution read at an arbitrary cardinal bound,
  `CommAlgCat.standardResolutionCotangentDerivedLowerShriekIsoOfLE`; both are in
  `StacksFrontier.Cotangent.ResolutionCotangentDerived`.
* `CommAlgCat.derivedCotangentComplexBaseChangeIso`: an identification of the two *objects*. This
  does **not** carry [Stacks, Tag 08QQ]: the lemma asserts that the functoriality map induces the
  isomorphism, and this one is not compared with it. See the implementation notes below.
* `CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso` and
  `CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso_hom`: **[Stacks, Tag 08QQ]** with
  the arrow the source names — the isomorphism is induced by the functoriality map of the square.

## Implementation notes

**Two isomorphisms, and which one is the source's arrow.** The source says that *the
functoriality map* induces the isomorphism. That statement is
`CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso`, whose underlying morphism is by
construction the image in `D(B')` of `CommAlgCat.cotangentExtendScalarsComplexMap`, the map of
[Stacks, Tag 08PN] after extension of scalars; it rests on
`CommAlgCat.quasiIso_cotangentExtendScalarsComplexMap` of
`StacksFrontier.Cotangent.BaseChangeQuasiIso`, which shows that map is a quasi-isomorphism.

`CommAlgCat.derivedCotangentComplexBaseChangeIso`, proved here by the site-theoretic route, is an
isomorphism between the same two objects that is *not* compared with the functoriality map. The
obstruction is in its input: [Stacks, Tag 08PU] in `D(B)`,
`CommAlgCat.standardResolutionCotangentDerivedLowerShriekIso`, is produced from a chosen
projective resolution of the coefficient sheaf and is therefore not natural *in the sheaf* — see
the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedColimitByPointResolution.lean`.
(It *is* natural in the point resolution, which is
`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality`; that is what
`StacksFrontier.Cotangent.ResolutionIndependence` uses, and it is what makes the functoriality route
above unconditional.) The two uses of the comparison below are at two different point resolutions
of the *same* site with the *same* sheaf, but they are matched through the base-change functor of
the sites rather than through a morphism of point resolutions, so the naturality available does
not identify them.

**One cardinal bound for both sites.** The small model of the footnote-restricted site is indexed
by a cardinal bounding the sets of variables, and the two halves of the argument need the *same*
bound on the site `C_{B'/A'}`: one for the base change of the standard resolution of `B` over `A`,
which has the same variables as the latter, and one for the standard resolution of `B'` over `A'`.
The proof therefore works at `max (standardResolutionVarCardinal A B)
(standardResolutionVarCardinal A' B')`, and
`CommAlgCat.standardResolutionCotangentDerivedLowerShriekIsoOfLE` relaxes the bound of
`CommAlgCat.standardResolutionCotangentDerivedLowerShriekIso` to make this possible. No cardinal
appears in the statement of Tag 08QQ.

**The hypothesis.** As in [Stacks, Tag 08QP], the hypothesis that the square induce a
quasi-isomorphism `B ⊗_A^𝐋 A' = B'` is spelled out by the equivalent conjunction of the vanishing
of the higher Tor groups `Tor_i^A(A', B)` and the bijectivity of `A' ⊗_A B → B'`. No further
hypothesis is imposed; in particular neither map of the square is assumed flat or of finite type.

## References

* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
* [Stacks Project, Tag 08Q8](https://stacks.math.columbia.edu/tag/08Q8)
* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
* [Stacks Project, Tag 08QP](https://stacks.math.columbia.edu/tag/08QP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace ComplexShape.Embedding

section Extend

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  {A D : Type*} [Category* A] [Category* D] [Preadditive A] [Preadditive D]
  [HasZeroObject A] [HasZeroObject D] (F : A ⥤ D) [F.Additive]

/-- **Applying an additive functor to the auxiliary objects of an extended complex.** The terms
of `HomologicalComplex.extend` are indexed by `Option ι`, with the value at `none` the zero
object; an additive functor preserves the value at `some i` on the nose and the zero object up to
the canonical isomorphism. -/
def extendXMapIso (K : HomologicalComplex A c) (o : Option ι) :
    F.obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) o :=
  match o with
  | some _ => Iso.refl _
  | none => F.mapZeroObject

/-- The isomorphisms of `ComplexShape.Embedding.extendXMapIso` are compatible with the auxiliary
differentials of an extended complex. -/
lemma extendXMapIso_comm (K : HomologicalComplex A c) (o p : Option ι) :
    F.map (HomologicalComplex.extend.d K o p) ≫ (extendXMapIso F K p).hom =
      (extendXMapIso F K o).hom ≫
        HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) o p := by
  match o, p with
  | none, _ =>
      rw [HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl,
        HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl, F.map_zero, zero_comp, comp_zero]
  | some _, none =>
      rw [HomologicalComplex.extend.d_none_eq_zero' _ _ _ rfl,
        HomologicalComplex.extend.d_none_eq_zero' _ _ _ rfl, F.map_zero, zero_comp, comp_zero]
  | some a, some b =>
      show F.map (K.d a b) ≫ 𝟙 _ = 𝟙 _ ≫ F.map (K.d a b)
      rw [Category.comp_id, Category.id_comp]

/-- **An additive functor commutes with extension of complexes along an embedding of complex
shapes**: both sides are `F` applied degreewise in the degrees in the image of the embedding and
zero elsewhere. -/
def extendMapIso (K : HomologicalComplex A c) :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun i' => extendXMapIso F K (e.r i'))
    (fun i' j' _ => (extendXMapIso_comm F K (e.r i') (e.r j')).symm)

end Extend

end ComplexShape.Embedding

open scoped TensorProduct ChangeOfRings

universe u

namespace CommAlgCat

/-! ### Tag 08QQ -/

section DerivedPushout

attribute [local instance] HasDerivedCategory.standard

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
  [Algebra A (B' : Type u)] [IsScalarTower A A' (B' : Type u)]
  (b : (B : Type u) →ₐ[A] (B' : Type u)) (κ : Cardinal.{u})

variable {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- **The evaluation of `i^*Ω_{𝒪'/A'}` on the base change of a resolution.** The image under base
change of the cosimplicial object of `ε : P_• ⟶ B`, read in the small model of the restricted site
`C_{B'/A'}`, carries `i^*Ω_{𝒪'/A'}` to the simplicial `B'`-module `B' ⊗_{P'_•} Ω[P'_•⁄A']` of the
base-changed augmentation. This is `CommAlgCat.smallResolutionCotangentModuleIso` for the
base-changed resolution, read through
`CommAlgCat.smallResolutionCosimplicialObjectBaseChangeι`. -/
def smallResolutionBaseChangeCotangentModuleIso :
    (smallResolutionCosimplicialObject ε κ hPκ ⋙ smallPolynomialBaseChange b κ).op ⋙
        smallPolynomialCotangentModulePresheaf A' B' κ ≅
      resolutionOver (augmentationBaseChange b ε) ⋙ overDifferentialsFunctor :=
  Functor.isoWhiskerRight
    (NatIso.op (smallResolutionCosimplicialObjectBaseChangeι b κ ε hPκ)).symm
    (polynomialCotangentModulePresheaf A' B')

variable {κ}

/-- **The simplicial `B'`-module of the base-changed resolution.** Extending the scalars of the
simplicial `B`-module `B ⊗_{P_•} Ω[P_•⁄A]` of [Stacks, Tag 08PN] to `B'` gives the evaluation of
`i^*Ω_{𝒪'/A'}` on the image of the resolution under the base-change functor of the sites. This
puts together the "direct inspection" isomorphism
`CommAlgCat.overDifferentialsBaseChangeNatIso` with the identification
`CommAlgCat.resolutionOver_augmentationBaseChange` of the base change of the resolution. -/
def cotangentSimplicialModuleBaseChangeIso
    (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ ((standardResolution.{u, u} A B).left.obj n)) :
    (cotangentSimplicialModule.{u, u} A B).object ⋙
        ModuleCat.extendScalars b.toRingHom ≅
      (smallResolutionCosimplicialObject (standardResolution.{u, u} A B).hom κ hPκ ⋙
          smallPolynomialBaseChange b κ).op ⋙
        smallPolynomialCotangentModulePresheaf A' B' κ :=
  (Functor.isoWhiskerRight (standardResolutionOverDifferentialsIso A B)
      (ModuleCat.extendScalars b.toRingHom)).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (resolutionOver (standardResolution.{u, u} A B).hom)
      (overDifferentialsBaseChangeNatIso b) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    (smallResolutionBaseChangeCotangentModuleIso b κ (standardResolution.{u, u} A B).hom
      hPκ).symm

/-- **The degreewise base change of the cotangent complex computes `Lπ'_!(Ω_{𝒪'/A'} ⊗_{𝒪'} B̲')`.**
If the base change of the standard resolution of `B` over `A` is again a resolution of `B'` over
`A'`, then its cosimplicial object is a point resolution of the small model of the restricted site
`C_{B'/A'}` (`CommAlgCat.isPointResolution_smallPolynomialBaseChange`, which is the content of
[Stacks, Tag 08QP]), and the evaluation of `i^*Ω_{𝒪'/A'}` on it is the degreewise base change
`B' ⊗_B L_{B/A}`. So the derived form of [Stacks, Tag 08PT] identifies the latter with
`Lπ'_!(Ω_{𝒪'/A'} ⊗_{𝒪'} B̲')` in `D(B')`. -/
def extendScalarsCotangentComplexDerivedLowerShriekIso
    (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ ((standardResolution.{u, u} A B).left.obj n))
    (hres : IsResolution A' (B' : Type u)
      (simplicialBaseChange b (standardResolution.{u, u} A B).hom)
      (augmentationBaseChange b (standardResolution.{u, u} A B).hom)) :
    DerivedCategory.Q.obj
        (((ModuleCat.extendScalars b.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) ≅
      smallPolynomialCotangentDerivedLowerShriek A' B' κ :=
  DerivedCategory.Q.mapIso (ComplexShape.Embedding.extendMapIso
      (ComplexShape.embeddingUpIntLE (0 : ℤ)) (ModuleCat.extendScalars b.toRingHom)
      ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
        (cotangentSimplicialModule.{u, u} A B).object)) ≪≫
    DerivedCategory.Q.mapIso
      (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
        (ModuleCat.{u} (B' : Type u))).mapIso
          ((alternatingFaceMapComplexCompMapHomologicalComplexIso
              (ModuleCat.extendScalars b.toRingHom)).app
            (cotangentSimplicialModule.{u, u} A B).object ≪≫
          (alternatingFaceMapComplex (ModuleCat.{u} (B' : Type u))).mapIso
            (cotangentSimplicialModuleBaseChangeIso b hPκ))) ≪≫
    Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit
      (smallResolutionCosimplicialObject (standardResolution.{u, u} A B).hom κ hPκ ⋙
        smallPolynomialBaseChange b κ)
      (smallPolynomialCotangentModulePresheaf A' B' κ)
      (isPointResolution_smallPolynomialBaseChange b κ (standardResolution.{u, u} A B).hom
        hPκ hres)

/-- **The derived base change of the cotangent complex is its degreewise base change.** The
cotangent complex is a bounded above complex of free modules, so the comparison map of the total
derived extension-of-scalars functor is invertible at it; this is
`CommAlgCat.nonempty_derivedExtensionScalars_cotangentComplex_iso` with the isomorphism named. -/
def derivedExtensionScalarsCotangentComplexIso :
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
          b.toRingHom).functor.obj (DerivedCategory.Q.obj (cotangentComplex.{u, u} A B)) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars b.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A B)) := by
  have hproj : ∀ i : ℤ, Projective ((cotangentComplex.{u, u} A B).X i) :=
    projective_cotangentComplex_X'.{u, u} A B
  have := hproj
  have hIso : IsIso ((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
      b.toRingHom).comparison.app (cotangentComplex.{u, u} A B)) :=
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
      b.toRingHom).comparison_isIso_of_projective (cotangentComplex.{u, u} A B) 0
  exact @asIso _ _ _ _ _ hIso

/-- **[Stacks, Tag 08QQ].** Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings which induces a quasi-isomorphism `B ⊗_A^𝐋 A' = B'` — that is,
`Tor_i^A(A', B) = 0` for `i > 0` and the canonical map `A' ⊗_A B → B'` is bijective. Then

`L_{B/A} ⊗^𝐋_B B' = L_{B'/A'}`

in `D(B')`, where `- ⊗^𝐋_B B'` is the total derived extension-of-scalars functor of
`StacksFrontier.Homology.Tor.DerivedExtensionScalars`.

The proof is the source's. The cotangent complex is a bounded above complex of free modules, so
`L_{B/A} ⊗^𝐋_B B'` is the degreewise base change `B' ⊗_B L_{B/A}`
(`CommAlgCat.derivedExtensionScalarsCotangentComplexIso`). By the "direct inspection" of the source
(`CommAlgCat.overDifferentialsBaseChangeNatIso`) that complex is the extended Moore complex of
`i^*Ω_{𝒪'/A'}` evaluated on the image of the standard resolution of `B` over `A` under the
base-change functor of the sites of [Stacks, Tag 08QN]. The hypothesis makes that image a
resolution of `B'` over `A'` (`CommAlgCat.isResolution_augmentationBaseChange`) and hence a point
resolution of the site `C_{B'/A'}`
(`CommAlgCat.isPointResolution_smallPolynomialBaseChange`, the content of [Stacks, Tag 08QP]), so
the derived form of [Stacks, Tag 08PT] computes `Lπ'_!(Ω_{𝒪'/A'} ⊗_{𝒪'} B̲')` by it; and
[Stacks, Tag 08PU] in `D(B')`, read at the same cardinal bound
(`CommAlgCat.standardResolutionCotangentDerivedLowerShriekIsoOfLE`), identifies that with
`L_{B'/A'}`.

Both sites are read at the small model of the footnote-restricted site, at the common bound
`max (standardResolutionVarCardinal A B) (standardResolutionVarCardinal A' B')`; the bound does
not appear in the statement.

The isomorphism produced here is *not* identified with the chain-level functoriality map
`CommAlgCat.squareCotangentComplexMap` of [Stacks, Tag 08PN]; see the implementation notes of
this module. For the isomorphism that *is* induced by the functoriality map, which is what the
source asserts, see `CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso` below. -/
-- No `@[stacks 08QQ]`. Tag 08QQ asserts that **the functoriality map** induces an isomorphism
-- `L_{B/A} ⊗^𝐋_B B' ⟶ L_{B'/A'}`; which morphism realizes the isomorphism is part of the
-- assertion, not incidental to it. The isomorphism built here goes by the site-theoretic route
-- and is not compared with the functoriality map — nor can it be with the naturality available,
-- for the reason set out in the implementation notes of this module: [Stacks, Tag 08PU] in
-- `D(B)` is produced from a chosen projective resolution of the coefficient sheaf and is
-- therefore not natural in the sheaf. So this declaration states strictly less than the lemma:
-- an isomorphism between the two objects, with no claim about which morphism realizes it.
-- Tag 08QQ is carried by `CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso` and
-- `CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso_hom` below, which state the
-- lemma with the source's own arrow, and in `StacksFrontier.Cotangent.BaseChangeQuasiIso` by
-- `CommAlgCat.quasiIso_cotangentExtendScalarsComplexMap` and
-- `CommAlgCat.cotangentBaseChangeIso`.
def derivedCotangentComplexBaseChangeIso
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective (baseChangeUnit b)) :
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
          b.toRingHom).functor.obj (DerivedCategory.Q.obj (cotangentComplex.{u, u} A B)) ≅
      DerivedCategory.Q.obj (cotangentComplex.{u, u} A' B') :=
  derivedExtensionScalarsCotangentComplexIso b ≪≫
    extendScalarsCotangentComplexDerivedLowerShriekIso b
      (fun n => (standardResolution_isPolynomialAlgebraBelow A B n).mono (le_max_left _ _))
      (isResolution_augmentationBaseChange b (standardResolution.{u, u} A B).hom
        (standardResolution_isResolution.{u, u} A B) hTor hφ) ≪≫
    (standardResolutionCotangentDerivedLowerShriekIsoOfLE A' B' _ (le_max_right _ _)).symm

/-- **[Stacks, Tag 08QQ].** Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings which induces a quasi-isomorphism `B ⊗_A^𝐋 A' = B'` — that is,
`Tor_i^A(A', B) = 0` for `i > 0` and the canonical map `A' ⊗_A B → B'` is bijective. Then the
functoriality map induces an isomorphism

`L_{B/A} ⊗^𝐋_B B' ⟶ L_{B'/A'}`

in `D(B')`, where `- ⊗^𝐋_B B'` is the total derived extension-of-scalars functor of
`StacksFrontier.Homology.Tor.DerivedExtensionScalars`.

The arrow is the source's. The cotangent complex is a bounded above complex of free modules, so
`L_{B/A} ⊗^𝐋_B B'` is the degreewise base change `B' ⊗_B L_{B/A}`
(`CommAlgCat.derivedExtensionScalarsCotangentComplexIso`), and on that the functoriality map of
[Stacks, Tag 08PN] after extension of scalars is
`CommAlgCat.cotangentExtendScalarsComplexMap`, a quasi-isomorphism by
`CommAlgCat.quasiIso_cotangentExtendScalarsComplexMap`. That the isomorphism built here is
induced by the functoriality map and not merely some isomorphism between the two objects is
`CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso_hom`. -/
@[stacks 08QQ "the lemma, with the arrow the source names: under the source's own hypothesis \
  that the square induce a quasi-isomorphism B ⊗_A^L A' = B' — written out as vanishing of the \
  positive Tor_i^A(A', B) together with bijectivity of A' ⊗_A B → B' — THE functoriality map of \
  Tag 08PN induces an isomorphism L_{B/A} ⊗^L_B B' ≅ L_{B'/A'} in D(B'), the derived tensor \
  product being the chapter's total derived extension-of-scalars functor. That the underlying \
  morphism is that functoriality map is \
  CommAlgCat.derivedCotangentComplexBaseChangeFunctorialityIso_hom below. No hypothesis beyond \
  the source's is carried: Remark 08QI is proved, not assumed \
  (CommAlgCat.cotangentComputedByEveryResolution)"]
def derivedCotangentComplexBaseChangeFunctorialityIso
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective (baseChangeUnit b)) :
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral
          b.toRingHom).functor.obj (DerivedCategory.Q.obj (cotangentComplex.{u, u} A B)) ≅
      DerivedCategory.Q.obj (cotangentComplex.{u, u} A' B') :=
  derivedExtensionScalarsCotangentComplexIso b ≪≫ cotangentBaseChangeIsoUnconditional b hTor hφ

/-- **The isomorphism of Tag 08QQ is the one the functoriality map induces.** Its underlying
morphism is the image in `D(B')` of `CommAlgCat.cotangentExtendScalarsComplexMap` — the
`B'`-linear adjoint of the `B`-linear map `L_{B/A} ⟶ L_{B'/A'}` of [Stacks, Tag 08PN] — read
after the identification of `L_{B/A} ⊗^𝐋_B B'` with the degreewise base change `B' ⊗_B L_{B/A}`.
-/
@[stacks 08QQ "that the isomorphism is induced by THE functoriality map of Tag 08PN: its \
  underlying morphism in D(B') is the image of the chain-level map \
  CommAlgCat.cotangentExtendScalarsComplexMap, read after the canonical identification of \
  L_{B/A} ⊗^L_B B' with the degreewise base change"]
theorem derivedCotangentComplexBaseChangeFunctorialityIso_hom
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective (baseChangeUnit b)) :
    (derivedCotangentComplexBaseChangeFunctorialityIso b hTor hφ).hom =
      (derivedExtensionScalarsCotangentComplexIso b).hom ≫
        DerivedCategory.Q.map (cotangentExtendScalarsComplexMap b) :=
  rfl

end DerivedPushout

end CommAlgCat

end
