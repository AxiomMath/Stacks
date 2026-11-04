module

public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionAgreementCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportEtaleLocalHigher
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupportVanishingOutside
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtalePostcomp

/-!
# Cohomology with support is unchanged by an étale morphism which is an isomorphism over the
subspace

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`, let `iY : Z ⟶ Y` be
a closed subspace and let `iX : W ⟶ X` be its inverse image, carried isomorphically onto it by
`k : W ⟶ Z`.  This file proves the **second conclusion of Stacks 0A4P**: for every abelian sheaf
`F` on the small étale site of `Y` and every degree `q`,

`H^q_Z(Y, F) = H^q_{f⁻¹Z}(X, f⁻¹F)`,

naturally in `F`.

## The excision argument

The identity is a statement about *global* sections, so it needs a covering of `Y` itself, and
the small étale site has no object `Y` to cover: its objects are étale scheme charts, so
`CategoryTheory.Sheaf.Γ` there is a limit over the whole site and evaluation nowhere.  The
argument is therefore run on the spaces-étale site of Stacks 03G0, which has the same topos by
Stacks 03G1 and in which `Y` *is* the terminal object:

* `AlgebraicGeometry.Space.ΓTerminalNatIso` identifies global sections over the small étale site
  of the restriction of a spaces-étale sheaf with its sections at the terminal object;
* `AlgebraicGeometry.Space.isCovering_excisionCover` says that `X` and the open complement
  `Y ∖ Z` cover `Y` in the spaces-étale topology — this is the first of the two uses of the
  hypothesis on `k`, which makes `|f|` reach every point of `Z` even though `f` is not
  surjective;
* the sections of `ℋ_Z(F)` over an object missing `Z` vanish, by
  `AlgebraicGeometry.Space.isZero_obj_of_spacesEtaleChartRestriction_iso`, so the second member
  of the covering and every overlap involving it contribute nothing;
* the one remaining compatibility is that two morphisms `V ⟶ X` over `Y` restrict a section of
  `ℋ_Z(F)` over `X` to the same section over `V`, which is
  `AlgebraicGeometry.Space.map_eq_of_hom_etaleObject` — the second use of the hypothesis on `k`.

So the sheaf condition for the two-element excision covering makes restriction from `Y` to `X`
an isomorphism on the sections of the spaces-étale avatar of `ℋ_Z(F)`, which is exactly the
degree-zero identity `Γ_Z(Y, F) = Γ_{f⁻¹Z}(X, f⁻¹F)`.  The passage to all degrees is the source's
own argument and the one already used for the sheaf-level conclusion in
`StacksFrontier/AlgebraicGeometry/Spaces/SectionsWithSupportEtaleLocalHigher.lean`: `f⁻¹` is exact
and preserves injective abelian sheaves, so it comes out of a right derived functor
(Stacks 015Z).

## Main definitions

* `AlgebraicGeometry.Space.spacesSectionsWithSupportInClosedSubspace`: the spaces-étale avatar
  of `ℋ_Z`, that is `ℋ_Z` followed by the inverse of the equivalence of Stacks 03G1.
* `AlgebraicGeometry.Space.terminalToEtaleObjectRestriction`: restriction of sections from the
  terminal object of the spaces-étale site of `Y` to `X`.

## Main results

* `AlgebraicGeometry.Space.isIso_map_from_idObj`: **the excision isomorphism.**  For a
  spaces-étale sheaf vanishing on every object missing `Z`, restriction from the terminal object
  to `X` is an isomorphism.
* `AlgebraicGeometry.Space.closedGlobalSectionsWithSupportEtaleExcisionIso`: **Stacks 0A4P,
  conclusion (2) in degree zero**, `Γ_Z(Y, F) = Γ_{f⁻¹Z}(X, f⁻¹F)`.
* `AlgebraicGeometry.Space.closedCohomologyWithSupportEtaleExcisionIso`: **Stacks 0A4P,
  conclusion (2)**, `H^q_Z(Y, F) = H^q_{f⁻¹Z}(X, f⁻¹F)` in every degree.

## Implementation notes

The three transports in the degree-zero comparison are all *equalities* of functors holding by
`rfl`, which is what keeps the chain free of coherence data:
`AlgebraicGeometry.Space.comparisonFunctor_comp_spacesEtalePostcomp` makes restriction along
spaces-étale postcomposition followed by restriction to the charts of `X` equal to restriction
to the charts of `Y` followed by `f⁻¹`, because
`CategoryTheory.Functor.sheafPushforwardContinuousComp` is the identity isomorphism; and
spaces-étale postcomposition carries the terminal object of the spaces-étale site of `X` to `X`
viewed over `Y`, again on the nose.  So only the two instances of `ΓTerminalNatIso`, the counit
of the equivalence of Stacks 03G1, and the degree-zero comparison of sections with support
appear.

The excision isomorphism is proved at an arbitrary coefficient category and with the vanishing
as a hypothesis, so it carries no sheaf-theoretic size conditions; the abelian specialisation
supplies the vanishing from
`AlgebraicGeometry.Space.isZero_obj_of_spacesEtaleChartRestriction_iso`.

Only the inverse image `f⁻¹` of abelian sheaves appears; no extension by zero and no
compatibility of global sections with a closed immersion is used.

## References

* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4P](https://stacks.math.columbia.edu/tag/0A4P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The excision isomorphism -/

section Excision

variable {W X Y Z : AlgebraicSpaces B S hS}

/-- The image of an object of the spaces-étale site lies in the image of any object it maps
to: a morphism of the site is a morphism over the base. -/
theorem range_pointsMap_le_of_spacesEtale_hom {V V' : SpacesEtale B S hS Y} (g : V ⟶ V') :
    Set.range (pointsMap B S hS ((SpacesEtale.toSpaces B S hS Y).obj V).1 V.1.hom.hom) ⊆
      Set.range (pointsMap B S hS ((SpacesEtale.toSpaces B S hS Y).obj V').1 V'.1.hom.hom) := by
  have hw : ((SpacesEtale.toSpaces B S hS Y).map g).hom ≫ V'.1.hom.hom = V.1.hom.hom :=
    congrArg (fun q => q.hom) (Over.w ((SpacesEtale.inclusion B S hS Y).map g))
  rintro x ⟨y, rfl⟩
  exact ⟨pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS Y).map g).hom y,
    (pointsMap_comp_apply B S hS _ _ y).symm.trans
      (congrArg (fun q => pointsMap B S hS _ q y) hw)⟩

variable (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (iY : Z ⟶ Y)
    (hiY : IsClosedImmersion B S hS iY.hom) {iX : W ⟶ X} {k : W ⟶ Z} [IsIso k]

include hiY in
/-- **The excision isomorphism of Stacks 0A4P.**  Let `Q` be a sheaf on the spaces-étale site of
`Y`, with values in an arbitrary category, which vanishes on every object of the site whose
image misses `Z`.  Then restriction of sections from the terminal object `Y` to `X` is an
isomorphism `Q(Y) ≅ Q(X)`.

Its inverse is the amalgamation, over the two-element excision covering
`AlgebraicGeometry.Space.excisionCover`, of the identity of `Q(X)` and of the unique morphism
into the zero group `Q(Y ∖ Z)`.  Of the four compatibility conditions three are vacuous because
their common source maps into the complement of `Z`, where `Q` vanishes, and the fourth is
`AlgebraicGeometry.Space.map_eq_of_hom_etaleObject`. -/
theorem isIso_map_from_idObj {A : Type w} [Category.{w'} A]
    (Q : Sheaf (SpacesEtale.topology B S hS Y) A)
    (hzero : ∀ V' : SpacesEtale B S hS Y,
      Set.range (pointsMap B S hS ((SpacesEtale.toSpaces B S hS Y).obj V').1 V'.1.hom.hom) ⊆
          (Set.range (pointsMap B S hS Z.1 iY.hom))ᶜ →
        IsZero (Q.obj.obj (op V')))
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    IsIso (Q.obj.map ((SpacesEtale.isTerminal_idObj B S hS Y).from
      (etaleObject B S hS f hf)).op) := by
  set E := excisionCover B S hS f hf iY hiY
  have hmem : Sieve.ofArrows E.X E.f ∈
      SpacesEtale.topology B S hS Y (SpacesEtale.idObj B S hS Y) :=
    generate_excisionCover_mem_topology B S hS f hf iY hiY hk
  -- Anything mapping to the open complement of `Z` misses `Z`, so `Q` vanishes on it.
  have hzeroW : ∀ (V' : SpacesEtale B S hS Y) (i : ULift.{u + 1} Bool),
      i.down = false → (V' ⟶ E.X i) → IsZero (Q.obj.obj (op V')) := by
    intro V' i hi b
    refine hzero V' ((range_pointsMap_le_of_spacesEtale_hom B S hS b).trans ?_)
    obtain ⟨i⟩ := i
    cases i with
    | false => exact le_of_eq (range_pointsMap_complementHom B S hS iY hiY)
    | true => exact absurd hi (by simp)
  have hcompl : IsZero (Q.obj.obj (op (complementObj B S hS iY hiY))) :=
    hzeroW _ (ULift.up false) rfl (𝟙 _)
  -- The compatible family: the identity on `X`, and the unique morphism to the zero group on
  -- the open complement of `Z`.
  set x : ∀ i : ULift.{u + 1} Bool, Q.obj.obj (op (etaleObject B S hS f hf)) ⟶
      Q.obj.obj (op (E.X i)) := fun i =>
    Bool.rec (motive := fun b => Q.obj.obj (op (etaleObject B S hS f hf)) ⟶
        Q.obj.obj (op (Bool.rec (complementObj B S hS iY hiY)
          (etaleObject B S hS f hf) b : SpacesEtale B S hS Y)))
      (hcompl.from_ _) (𝟙 _) i.down
  have hcompat : ∀ ⦃V' : SpacesEtale B S hS Y⦄ ⦃i j : ULift.{u + 1} Bool⦄
      (a : V' ⟶ E.X i) (b : V' ⟶ E.X j), a ≫ E.f i = b ≫ E.f j →
      x i ≫ Q.obj.map a.op = x j ≫ Q.obj.map b.op := by
    rintro V' ⟨i⟩ ⟨j⟩ a b -
    cases i with
    | false => exact (hzeroW V' (ULift.up false) rfl a).eq_of_tgt _ _
    | true =>
        cases j with
        | false => exact (hzeroW V' (ULift.up false) rfl b).eq_of_tgt _ _
        | true =>
            exact congrArg (fun m => x (ULift.up true) ≫ m)
              (map_eq_of_hom_etaleObject B S hS f hf iY hiY V' a b Q hzero hk)
  have hamal := Q.property.amalgamateOfArrows_map E.f hmem x hcompat (ULift.up true)
  refine ⟨Q.property.amalgamateOfArrows E.f hmem x hcompat, ?_, ?_⟩
  · refine Q.property.hom_ext_ofArrows E.f hmem ?_
    rintro ⟨i⟩
    cases i with
    | false => exact hcompl.eq_of_tgt _ _
    | true =>
        rw [Category.assoc, hamal, Category.id_comp]
        exact Category.comp_id _
  · exact hamal

end Excision

/-! ### The degree-zero identity -/

section DegreeZero

variable {W X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (iY : Z ⟶ Y) (hiY : IsClosedImmersion B S hS iY.hom)

/-- **The spaces-étale avatar of `ℋ_Z`.**  The subsheaf of sections with support in the closed
subspace `Z`, transported along the inverse of the equivalence of Stacks 03G1 to a sheaf on the
spaces-étale site of `Y`, where `Y` itself is an object. -/
abbrev spacesSectionsWithSupportInClosedSubspace :
    Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1} :=
  closedSectionsWithSupport.{u + 1} B S hS iY ⋙
    (spacesEtaleChartRestriction B S hS Y (A := AddCommGrpCat.{u + 1})).inv

/-- Restriction of sections from the terminal object of the spaces-étale site of `Y` to `X`
viewed over `Y`. -/
abbrev terminalToEtaleObjectRestriction :
    (sheafSections (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}).obj
        (op (SpacesEtale.idObj B S hS Y)) ⟶
      (sheafSections (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}).obj
        (op (etaleObject B S hS f hf)) :=
  (sheafSections (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}).map
    ((SpacesEtale.isTerminal_idObj B S hS Y).from (etaleObject B S hS f hf)).op

/-- The spaces-étale avatar of `ℋ_Z(F)` vanishes on every object of the spaces-étale site whose
image misses `Z`: its restriction to the charts is `ℋ_Z(F)` itself, by the counit of the
equivalence of Stacks 03G1. -/
theorem isZero_obj_spacesSectionsWithSupportInClosedSubspace
    (G : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (V : SpacesEtale B S hS Y)
    (hV : Set.range (pointsMap B S hS ((SpacesEtale.toSpaces B S hS Y).obj V).1 V.1.hom.hom) ⊆
      (Set.range (pointsMap B S hS Z.1 iY.hom))ᶜ) :
    IsZero (((spacesSectionsWithSupportInClosedSubspace B S hS iY).obj G).obj.obj (op V)) :=
  isZero_obj_of_spacesEtaleChartRestriction_iso B S hS Y
    (Set.range (pointsMap B S hS Z.1 iY.hom)) G _
    ((spacesEtaleChartRestriction B S hS Y (A := AddCommGrpCat.{u + 1})).asEquivalence.counitIso.app
      ((closedSectionsWithSupport.{u + 1} B S hS iY).obj G)) V hV

variable {iX : W ⟶ X} {k : W ⟶ Z} [IsIso k]

include hiY in
/-- The excision isomorphism at the spaces-étale avatar of `ℋ_Z(F)`. -/
theorem isIso_terminalToEtaleObjectRestriction_app
    (hk : IsPullback k.hom iX.hom iY.hom f.hom)
    (G : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) :
    IsIso ((Functor.whiskerLeft (spacesSectionsWithSupportInClosedSubspace B S hS iY)
      (terminalToEtaleObjectRestriction B S hS f hf)).app G) :=
  isIso_map_from_idObj B S hS f hf iY hiY _
    (isZero_obj_spacesSectionsWithSupportInClosedSubspace B S hS iY G) hk

include hiY in
/-- **Restriction from `Y` to `X` is an isomorphism on the sections of the spaces-étale avatar of
`ℋ_Z`**, as a natural isomorphism of functors of the abelian sheaf. -/
def excisionNatIso (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    spacesSectionsWithSupportInClosedSubspace B S hS iY ⋙
        (sheafSections (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}).obj
          (op (SpacesEtale.idObj B S hS Y)) ≅
      spacesSectionsWithSupportInClosedSubspace B S hS iY ⋙
        (sheafSections (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}).obj
          (op (etaleObject B S hS f hf)) :=
  haveI : ∀ G, IsIso ((Functor.whiskerLeft
      (spacesSectionsWithSupportInClosedSubspace B S hS iY)
      (terminalToEtaleObjectRestriction B S hS f hf)).app G) :=
    isIso_terminalToEtaleObjectRestriction_app B S hS f hf iY hiY hk
  haveI : IsIso (Functor.whiskerLeft (spacesSectionsWithSupportInClosedSubspace B S hS iY)
      (terminalToEtaleObjectRestriction B S hS f hf)) := NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerLeft (spacesSectionsWithSupportInClosedSubspace B S hS iY)
    (terminalToEtaleObjectRestriction B S hS f hf))

/-- Global sections of `ℋ_Z(F)` over the small étale site of `Y` are its sections at the
terminal object of the spaces-étale site: `ΓTerminalNatIso` read through the counit of the
equivalence of Stacks 03G1. -/
def closedGlobalSectionsWithSupportTerminalIso :
    spacesSectionsWithSupportInClosedSubspace B S hS iY ⋙
        (sheafSections (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}).obj
          (op (SpacesEtale.idObj B S hS Y)) ≅
      closedGlobalSectionsWithSupport B S hS iY :=
  Functor.isoWhiskerLeft (closedSectionsWithSupport.{u + 1} B S hS iY)
    (Functor.isoWhiskerLeft (spacesEtaleChartRestriction B S hS Y (A := AddCommGrpCat.{u + 1})).inv
        (ΓTerminalNatIso B S hS Y) ≪≫
      Functor.isoWhiskerRight
        (spacesEtaleChartRestriction B S hS Y (A := AddCommGrpCat.{u + 1})).asEquivalence.counitIso
        (Sheaf.Γ (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) ≪≫
      (Sheaf.Γ (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}).leftUnitor)

/-- Sections at `X` of the spaces-étale avatar of `ℋ_Z(F)` are the global sections, over the
small étale site of `X`, of `f⁻¹ℋ_Z(F)`.

Both transports are equalities of functors: spaces-étale postcomposition carries the terminal
object of the spaces-étale site of `X` to `X` viewed over `Y`, and restriction along it followed
by restriction to the charts of `X` is restriction to the charts of `Y` followed by `f⁻¹`, by
`AlgebraicGeometry.Space.comparisonFunctor_comp_spacesEtalePostcomp`. -/
def etaleObjectSectionsIso :
    (spacesEtaleChartRestriction B S hS Y (A := AddCommGrpCat.{u + 1})).inv ⋙
        (sheafSections (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u + 1}).obj
          (op (etaleObject B S hS f hf)) ≅
      etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
        Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft
      ((spacesEtaleChartRestriction B S hS Y (A := AddCommGrpCat.{u + 1})).inv ⋙
        (spacesEtalePostcomp B S hS f hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y))
      (ΓTerminalNatIso B S hS X) ≪≫
    Functor.isoWhiskerRight
      (spacesEtaleChartRestriction B S hS Y (A := AddCommGrpCat.{u + 1})).asEquivalence.counitIso
      (etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
        Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) ≪≫
    (etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
      Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}).leftUnitor

include hiY in
/-- **Stacks 0A4P, conclusion (2) in degree zero.**  Let `f : X ⟶ Y` be an étale morphism of
algebraic spaces over `S`, let `iY : Z ⟶ Y` be a closed subspace and let `iX : W ⟶ X` be its
inverse image, carried isomorphically onto it by `k`.  Then for every abelian sheaf `F` on the
small étale site of `Y` the global sections with support in `Z` of `F` are the global sections
with support in `f⁻¹Z` of `f⁻¹F`:

`Γ_Z(Y, F) = Γ_{f⁻¹Z}(X, f⁻¹F)`,

naturally in `F`.

This is the sheaf condition for the excision covering `{X, Y ∖ Z}` of `Y` in the spaces-étale
topology, read through the two identifications of global sections with sections at a terminal
object. -/
def closedGlobalSectionsWithSupportEtaleExcisionIso
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) :
    closedGlobalSectionsWithSupport B S hS iY ≅
      etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
        closedGlobalSectionsWithSupport B S hS iX :=
  haveI hrange : Set.range (pointsMap B S hS W.1 iX.hom) =
      pointsMap B S hS X.1 f.hom ⁻¹' Set.range (pointsMap B S hS Z.1 iY.hom) := by
    have h := preimage_image_pointsMap_of_isPullback B S hS hk Set.univ
    simpa [Set.image_univ] using h.symm
  (closedGlobalSectionsWithSupportTerminalIso B S hS iY).symm ≪≫
    excisionNatIso B S hS f hf iY hiY hk ≪≫
    Functor.isoWhiskerLeft (closedSectionsWithSupport.{u + 1} B S hS iY)
      (etaleObjectSectionsIso B S hS f hf) ≪≫
    Functor.isoWhiskerRight
      (sectionsWithSupportEtaleRestrictionIso.{u + 1} B S hS f hf
        (Set.range (pointsMap B S hS Z.1 iY.hom)))
      (Sheaf.Γ (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1}) ≪≫
    Functor.isoWhiskerLeft (etaleAbelianRestriction.{u + 1} B S hS f hf)
      (eqToIso (congrArg (fun T => globalSectionsWithSupport B S hS X.1 T) hrange.symm))

end DegreeZero

/-! ### The identity in every degree -/

section EveryDegree

variable {W X Y Z : AlgebraicSpaces B S hS}

/-- **Stacks 0A4P, conclusion (2): the global cohomology-with-support identity, in every
degree.**  Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over `S`, let `iY : Z ⟶ Y`
be a closed subspace and let `iX : W ⟶ X` be its inverse image, presented by the cartesian
square `hk` and carried isomorphically onto `Z` by `k`.  Then for every abelian sheaf `F` on the
small étale site of `Y` and every degree `q`,

`H^q_Z(Y, F) = H^q_{f⁻¹Z}(X, f⁻¹F)`,

naturally in `F`.

In degree zero this is
`AlgebraicGeometry.Space.closedGlobalSectionsWithSupportEtaleExcisionIso`, the source's excision
argument on the spaces-étale site.  The passage to all degrees is the source's own reasoning,
Stacks 015Z: inverse image along an étale morphism is exact and preserves injective abelian
sheaves, so it comes out of the right derived functor of the composite. -/
@[stacks 0A4P
  "conclusion (2), every degree q: H^q_Z(Y, F) = H^q_{f⁻¹Z}(X, f⁻¹F) for f étale and f⁻¹Z ≅ Z"]
def closedCohomologyWithSupportEtaleExcisionIso (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (iY : Z ⟶ Y) (hiY : IsClosedImmersion B S hS iY.hom) (iX : W ⟶ X) (k : W ⟶ Z) [IsIso k]
    (hk : IsPullback k.hom iX.hom iY.hom f.hom) (q : ℕ) :
    closedCohomologyWithSupport B S hS iY q ≅
      etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
        closedCohomologyWithSupport B S hS iX q :=
  haveI := preservesFiniteColimits_etaleAbelianRestriction B S hS f hf
  haveI := preservesInjectiveObjects_etaleAbelianRestriction B S hS f hf
  haveI : (etaleAbelianRestriction.{u + 1} B S hS f hf ⋙
      closedGlobalSectionsWithSupport B S hS iX).Additive := inferInstance
  Functor.rightDerivedIsoOfNatIso
      (closedGlobalSectionsWithSupportEtaleExcisionIso B S hS f hf iY hiY hk) q ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (etaleAbelianRestriction.{u + 1} B S hS f hf)
      (closedGlobalSectionsWithSupport B S hS iX) q

end EveryDegree

end AlgebraicGeometry.Space

end
