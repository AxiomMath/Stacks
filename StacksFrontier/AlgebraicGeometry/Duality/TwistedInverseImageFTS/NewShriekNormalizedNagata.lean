module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Duality.NewShriekPseudoFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NagataFormalism
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekProper
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedExistenceNagata
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedSeparatedNagata
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison

/-!
# `f_new^!` for the dualizing complexes normalized by Nagata compactifications

In Situation [Stacks, Tag 0AU4] (`S` Noetherian with a dualizing complex `ω_S^•`), let `ω_X^•`
be the dualizing complex normalized relative to `ω_S^•` for the upper shriek functors of Nagata
compactifications (`Stacks.Duality.normalizedDualizingComplex`, [Stacks, Tag 0AUA]), let
`D_X = R𝓗om(-, ω_X^•)` and `f_new^! = D_X ∘ Lf^* ∘ D_Y` (`Stacks.Duality.fNewShriekStd`), all at
the standard model of `D(𝒪_X)`. This file proves parts (2) to (6) of [Stacks, Tag 0AUE] and the
two halves of its closing remark (`ω_X^• = (X → S)^! ω_S^•` for `X` separated over `S`, and
`f_new^! = f^!`). Part (1) is `StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImageFTS/
NewShriekPseudofunctorNagata.lean`.

The upper shriek functors are the concrete ones, `Stacks.Duality.UpperShriek.nagata`: the
instance `Stacks.Duality.UpperShriek.ofCompactifications nagataCompactification` of the upper
shriek formalism, whose three fields are the functors `upperShriekPlus` of the Nagata
compactifications and the proved comparisons `factorIsoOf`, `factorIsoOf_assoc`
(`TwistedInverseImageFTS/Formalism.lean:160`), the compactifications being supplied by Nagata's
theorem (`Stacks.Duality.hasCompactification_of_isShriekable`,
`TwistedInverseImageFTS/NagataFormalism.lean:41`). No field of it is assumed.

The two inputs of parts (2) and (4) are proved here: `D_Y(ω_Y^•) ≅ 𝒪_Y` is the inverse of the
biduality `𝒪_Y ⟶ D_Y(D_Y(𝒪_Y)) = D_Y(ω_Y^•)` of [Stacks, Tag 0A89], invertible because `𝒪_Y` is
coherent; and `Lf^* 𝒪_Y ≅ 𝒪_X` is the unit comparison of the derived pullback.

## Main results

* `Stacks.Duality.NormalizedOnOpens.fNewShriekObjIsoNagata` — part (4).
* `Stacks.Duality.NormalizedOnOpens.fNewShriekStructureObjIsoNagata` — part (2).
* `Stacks.Duality.NormalizedOnOpens.coherentDuality_spec_nagata` — part (3).
* `Stacks.Duality.NormalizedOnOpens.fNewShriekPlusCohNagata` and
  `Stacks.Duality.NormalizedOnOpens.fNewShriekPlusCohNagata_obj` — part (5).
* `Stacks.Duality.NormalizedOnOpens.fNewShriekIsoRightAdjointNagata`,
  `Stacks.Duality.NormalizedOnOpens.fNewShriekSheafHomIsoNagata`,
  `Stacks.Duality.NormalizedOnOpens.sheafHomDualizingIsoOfMinusCohNagata` — part (6).
* `Stacks.Duality.existsUnique_iso_upperShriekPlus_of_isSeparated_nagata` — the closing
  remark, first half: `ω_X^• ≅ (X → S)^! ω_S^•` for `X` separated over `S`, at every
  compactification (from
  `Stacks.Duality.NormalizedOnOpens.existsUnique_iso_upperShriekPlus_nagata`).
* `Stacks.Duality.NormalizedOnOpens.upperShriekStdIsoFNewShriekNagata` — the closing remark,
  second half, `f_new^! = f^!` for every compactification of a separated `f`.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std sheafHom pull push comparison plusCoh qcoh
  rightAdjointStd plusCoh_le_qcoh IsDualizing stdMonoidal stdSymmetric stdMonoidalClosed)
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

section Unit

variable {X Y : Scheme.{u}}

/-- `Lf^* 𝒪_Y ≅ 𝒪_X` at the standard model: the unit comparison of the derived pullback. -/
def pullUnitIso (f : X ⟶ Y) : (pull f).obj (𝟙_ (Std Y)) ≅ 𝟙_ (Std X) :=
  Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso f.toLRSHom.toShHom

/-- The cohomology sheaves of `𝒪_X`, the unit of `D(𝒪_X)` at the standard model, are coherent
on a locally Noetherian scheme. -/
theorem isCoherent_homology_unit_std [IsLocallyNoetherian X] (i : ℤ) :
    ((@DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard X.Modules)
      i).obj (𝟙_ (Std X))).IsCoherent :=
  AlgebraicGeometry.TorFormula.isCoherent_homology_singleFunctor_obj X _
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit i

/-- **`R𝓗om(ω, ω) ≅ 𝒪` for a dualizing complex `ω`** ([Stacks, Tag 0A89]): `D(ω) ≅ D(D(𝒪))`
because `ω = R𝓗om(𝒪, ω)`, and the biduality `𝒪 ⟶ D(D(𝒪))` is invertible since `𝒪` is
coherent. -/
def dualIntoSelfIso [IsLocallyNoetherian Y] {ω : Std Y} (hω : IsDualizing ω) :
    (dualInto ω).obj (op ω) ≅ 𝟙_ (Std Y) :=
  (dualInto ω).mapIso (MonoidalClosed.unitIsoSelf (X := ω)).op ≪≫
    (@asIso _ _ _ _ ((bidualityNat ω).app (𝟙_ (Std Y)))
      (isIso_bidualityNat_app hω _ isCoherent_homology_unit_std)).symm

/-- `f_new^! ω_Y ≅ ω_X` for any `ω_X` and any dualizing `ω_Y`:
`D_X(Lf^* D_Y(ω_Y)) ≅ D_X(Lf^* 𝒪_Y) ≅ D_X(𝒪_X) ≅ ω_X`. -/
def fNewShriekStdObjIsoOfIsDualizing [IsLocallyNoetherian Y] (f : X ⟶ Y) (ωX : Std X)
    {ωY : Std Y} (hωY : IsDualizing ωY) :
    (fNewShriekStd f ωX ωY).obj ωY ≅ ωX :=
  ((dualInto ωX).mapIso ((pull f).mapIso (dualIntoSelfIso hωY) ≪≫ pullUnitIso f).op).symm ≪≫
    MonoidalClosed.unitIsoSelf (X := ωX)

end Unit

/-- A separated morphism between schemes of finite type over a Noetherian base is shriekable. -/
theorem isShriekable_of_isSeparated {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
    (hpe : f ≫ q = p) (hp : IsFiniteTypeOverNoetherian p) (hq : IsFiniteTypeOverNoetherian q)
    [IsSeparated f] : IsShriekable f :=
  have h := hp.of_comp' hq hpe
  { target_noetherian := h.base_noetherian
    separatedFiniteType := ⟨⟨inferInstance, h.locallyOfFiniteType⟩, h.quasiCompact⟩ }

/-- A separated morphism of finite type with Noetherian target is shriekable. -/
theorem isShriekable_of_isSeparated_of_isFiniteTypeOverNoetherian {X S : Scheme.{u}} {p : X ⟶ S}
    (hp : IsFiniteTypeOverNoetherian p) [IsSeparated p] : IsShriekable p :=
  { target_noetherian := hp.base_noetherian
    separatedFiniteType := ⟨⟨inferInstance, hp.locallyOfFiniteType⟩, hp.quasiCompact⟩ }

/-- **[Stacks, Tag 0AUE], the closing remark, first half.** In Situation 0AU4, if `X` is
separated over `S`, with structure morphism `p`, the dualizing complex `ω_X^•` normalized
relative to `ω_S^•` is canonically isomorphic to `p^! ω_S^•`, for the upper shriek functor `p^!`
of any compactification `j` of `p` ([Stacks, Tag 0A9Y]): exactly one isomorphism
`ω_X^• ≅ p^!_j ω_S^•` carries the normalization `α_W` of `ω_X^•` to the canonical
`(p^! ω_S^•)|_W ≅ (W → S)^! ω_S^•` for every open `W` separated over `S`. -/
@[stacks 0AUE "the closing remark, first half: omega_X = (X -> S)^! omega_S for X separated over S"]
theorem existsUnique_iso_upperShriekPlus_of_isSeparated_nagata {X S : Scheme.{u}} {p : X ⟶ S}
    {hp : IsFiniteTypeOverNoetherian p} {ωS : quasiCoherentDerivedCategoryPlusOfModel S}
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsSeparated p]
    (𝒦 : NormalizedOnOpens UpperShriek.nagata hp ωS) (j : CompactificationOf (Over.mk p)) :
    haveI := hp.base_noetherian
    ∃! e : 𝒦.complex ≅ (upperShriekPlus (ftsHomOf p
        (isShriekable_of_isSeparated_of_isFiniteTypeOverNoetherian hp).separatedFiniteType
        (isSeparatedFiniteType_id S) (Category.comp_id p)) j).obj ωS,
      ∀ (W : X.Opens) (hW : IsShriekable (W.ι ≫ p)),
        (UpperShriek.nagata.shriek W.ι (hp.isShriekable_ι W)).mapIso
            (e ≪≫ (DominatingCompactification.upperShriekPlusIso (ftsHomOf p
              (isShriekable_of_isSeparated_of_isFiniteTypeOverNoetherian hp).separatedFiniteType
              (isSeparatedFiniteType_id S) (Category.comp_id p)) j
              (nagataCompactification p
                (isShriekable_of_isSeparated_of_isFiniteTypeOverNoetherian hp))).app ωS) ≪≫
          upperShriekLocalIso UpperShriek.nagata hp
            (isShriekable_of_isSeparated_of_isFiniteTypeOverNoetherian hp) ωS hW =
        𝒦.localIso W hW :=
  NormalizedOnOpens.existsUnique_iso_upperShriekPlus_nagata hωS
    (isShriekable_of_isSeparated_of_isFiniteTypeOverNoetherian hp) 𝒦 j

namespace NormalizedOnOpens

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  {hp : IsFiniteTypeOverNoetherian p} {hq : IsFiniteTypeOverNoetherian q}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Tag 0AUE] part (4).** In Situation 0AU4, let `f : X ⟶ Y` be a morphism of schemes
of finite type over `S` and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to
`ω_S^•` (for the upper shriek functors of Nagata compactifications). Then
`ω_X^• ≅ f_new^! ω_Y^•`. -/
@[stacks 0AUE "part (4)"]
def fNewShriekObjIsoNagata (f : X ⟶ Y)
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    stdComplex nagataCompactification 𝒦X ≅
      (fNewShriekStd f (stdComplex nagataCompactification 𝒦X)
        (stdComplex nagataCompactification 𝒦Y)).obj (stdComplex nagataCompactification 𝒦Y) :=
  haveI := hq.source_noetherian
  (fNewShriekStdObjIsoOfIsDualizing f _
    (isDualizing_stdComplex nagataCompactification hωS 𝒦Y)).symm

/-- `ω_S^•` read at the standard model of `D(𝒪_S)`. -/
abbrev baseStdComplex (ωS : quasiCoherentDerivedCategoryPlusOfModel S) : Std S :=
  (comparison S).inverse.obj ωS.obj.obj

/-- **[Stacks, Tag 0AUE] part (2).** In Situation 0AU4, for `X` of finite type over `S` with
structure morphism `p : X ⟶ S` and `ω_X^•` the dualizing complex normalized relative to `ω_S^•`,
`ω_X^• ≅ (X → S)_new^! ω_S^•`, where `(X → S)_new^!` is formed with `ω_S^•` itself as the
normalized complex of `S`. -/
@[stacks 0AUE "part (2)"]
def fNewShriekStructureObjIsoNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS) :
    stdComplex nagataCompactification 𝒦X ≅
      (fNewShriekStd p (stdComplex nagataCompactification 𝒦X) (baseStdComplex ωS)).obj
        (baseStdComplex ωS) :=
  haveI := hp.base_noetherian
  (fNewShriekStdObjIsoOfIsDualizing p _
    (isDualizingComplex_standard_of_isDualizingComplex hωS)).symm

/-- **[Stacks, Tag 0AUE] part (3).** In Situation 0AU4, for `X` of finite type over `S` and
`ω_X^•` normalized relative to `ω_S^•`, the duality `D_X = R𝓗om(-, ω_X^•)` is an involution of
`D_Coh(𝒪_X)`: it carries `D_Coh(𝒪_X)` into itself, is an anti-equivalence of it with
`id ≅ D_X ∘ D_X` given by biduality, exchanges `D^+_Coh` and `D^-_Coh`, and is an
anti-equivalence of `D^b_Coh(𝒪_X)`. -/
@[stacks 0AUE "part (3)"]
theorem coherentDuality_spec_nagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦 : NormalizedOnOpens UpperShriek.nagata hp ωS) :
    haveI := hp.source_noetherian
    cohStd X (stdComplex nagataCompactification 𝒦) ∧
    (∀ M : Std X, cohStd X M →
      cohStd X ((dualInto (stdComplex nagataCompactification 𝒦)).obj (op M))) ∧
    (coherentDuality X
      (isDualizing_stdComplex nagataCompactification hωS 𝒦)).IsEquivalence ∧
    IsIso (coherentBiduality X
      (isDualizing_stdComplex nagataCompactification hωS 𝒦)) ∧
    (∀ M : Std X, cohStd X M →
      (plusCoh X M ↔
        minusCoh X ((dualInto (stdComplex nagataCompactification 𝒦)).obj (op M))) ∧
      (minusCoh X M ↔
        plusCoh X ((dualInto (stdComplex nagataCompactification 𝒦)).obj (op M)))) ∧
    (boundedCoherentDuality X
      (isDualizing_stdComplex nagataCompactification hωS 𝒦)).IsEquivalence :=
  coherentDuality_spec_stdComplex nagataCompactification hωS 𝒦

/-- `f_new^! = D_X ∘ Lf^* ∘ D_Y` as a functor `D^+_Coh(𝒪_Y) ⥤ D^+_Coh(𝒪_X)`, for the dualizing
complexes normalized relative to `ω_S^•`. -/
def fNewShriekPlusCohNagata (f : X ⟶ Y)
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    (plusCoh Y).FullSubcategory ⥤ (plusCoh X).FullSubcategory :=
  haveI := hp.source_noetherian
  haveI := hq.source_noetherian
  ObjectProperty.lift _ ((plusCoh Y).ι ⋙
      fNewShriekStd f (stdComplex nagataCompactification 𝒦X)
        (stdComplex nagataCompactification 𝒦Y))
    (fun M => plusCoh_fNewShriek f
      (isDualizing_stdComplex nagataCompactification hωS 𝒦X)
      (isDualizing_stdComplex nagataCompactification hωS 𝒦Y) M.obj
      M.property)

/-- **[Stacks, Tag 0AUE] part (5).** In Situation 0AU4, for a morphism `f : X ⟶ Y` of schemes of
finite type over `S`, `f_new^!` is a functor `D^+_Coh(𝒪_Y) ⥤ D^+_Coh(𝒪_X)` and
`f_new^! M = D_X(Lf^* D_Y(M))` for `M ∈ D^+_Coh(𝒪_Y)`: for such `M` the complex
`D_X(Lf^* D_Y(M))` lies in `D^+_Coh(𝒪_X)`, and it is the value of `f_new^!` at `M`. -/
@[stacks 0AUE "part (5)"]
theorem fNewShriekPlusCohNagata_obj (f : X ⟶ Y)
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) (M : (plusCoh Y).FullSubcategory) :
    plusCoh X ((dualInto (stdComplex nagataCompactification 𝒦X)).obj (op ((pull f).obj
        ((dualInto (stdComplex nagataCompactification 𝒦Y)).obj (op M.obj))))) ∧
      ((fNewShriekPlusCohNagata f hωS 𝒦X 𝒦Y).obj M).obj =
        (dualInto (stdComplex nagataCompactification 𝒦X)).obj (op ((pull f).obj
          ((dualInto (stdComplex nagataCompactification 𝒦Y)).obj (op M.obj)))) :=
  ⟨((fNewShriekPlusCohNagata f hωS 𝒦X 𝒦Y).obj M).property, rfl⟩

variable (hpe : f ≫ q = p)

/-- **[Stacks, Tag 0AUE] part (6), first assertion.** In Situation 0AU4, for a proper morphism
`f : X ⟶ Y` of schemes of finite type over `S` and the dualizing complexes `ω_X^•`, `ω_Y^•`
normalized relative to `ω_S^•`, `f_new^!` is isomorphic to the restriction to `D^+_Coh(𝒪_Y)` of
the right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` ([Stacks, Tag 0A9E]). -/
@[stacks 0AUE "part (6), first assertion"]
def fNewShriekIsoRightAdjointNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (plusCoh Y).ι ⋙ fNewShriekStd f (stdComplex nagataCompactification 𝒦X)
        (stdComplex nagataCompactification 𝒦Y) ≅
      ObjectProperty.ιOfLE plusCoh_le_qcoh ⋙ rightAdjointStd f :=
  fNewShriekIsoRightAdjointOfIsProper nagataCompactification hpe hωS 𝒦X 𝒦Y

/-- **[Stacks, Tag 0AUE] part (6), the duality isomorphism.** In Situation 0AU4, for a proper
morphism `f : X ⟶ Y` of schemes of finite type over `S`, `K ∈ D^-_Coh(𝒪_X)` and
`M ∈ D^+_Coh(𝒪_Y)`, there is a canonical isomorphism
`Rf_* R𝓗om(K, f_new^! M) ≅ R𝓗om(Rf_* K, M)`. -/
@[stacks 0AUE "part (6), the isomorphism Rf_* RHom(K, f_new^! M) = RHom(Rf_* K, M)"]
def fNewShriekSheafHomIsoNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS)
    (K : Std X) (hK : haveI := hp.source_noetherian; minusCoh X K)
    (M : (plusCoh Y).FullSubcategory) :
    (push f).obj (((sheafHom X).obj (op K)).obj
        ((fNewShriekStd f (stdComplex nagataCompactification 𝒦X)
          (stdComplex nagataCompactification 𝒦Y)).obj M.obj)) ≅
      ((sheafHom Y).obj (op ((push f).obj K))).obj M.obj :=
  fNewShriekSheafHomIso nagataCompactification hpe hωS 𝒦X 𝒦Y K hK M

/-- **[Stacks, Tag 0AUE] part (6), the duality for the dualizing complexes.** In Situation 0AU4,
for a proper morphism `f : X ⟶ Y` of schemes of finite type over `S` and `K ∈ D^-_Coh(𝒪_X)`,
`Rf_* R𝓗om(K, ω_X^•) ≅ R𝓗om(Rf_* K, ω_Y^•)`. -/
@[stacks 0AUE "part (6), the isomorphism Rf_* RHom(K, omega_X) = RHom(Rf_* K, omega_Y)"]
def sheafHomDualizingIsoOfMinusCohNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS)
    (K : Std X) (hK : haveI := hp.source_noetherian; minusCoh X K) :
    (push f).obj (((sheafHom X).obj (op K)).obj (stdComplex nagataCompactification 𝒦X)) ≅
      ((sheafHom Y).obj (op ((push f).obj K))).obj (stdComplex nagataCompactification 𝒦Y) :=
  sheafHomDualizingIso nagataCompactification hpe hωS 𝒦X 𝒦Y K hK

/-- **[Stacks, Tag 0AUE], the closing remark, `f_new^! = f^!`.** In Situation 0AU4, let
`f : X ⟶ Y` be a separated morphism of schemes of finite type over `S` (for instance a morphism
between schemes separated over `S`) and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized
relative to `ω_S^•`. For every compactification `j` of `f`, the upper shriek functor `f^!` of
`j` ([Stacks, Tag 0A9Y]) satisfies `f^! K ≅ f_new^! K`, naturally in `K ∈ D^+_Coh(𝒪_Y)`. -/
@[stacks 0AUE "the closing remark, second half: f_new^! K = f^! K for K in D^+_Coh"]
def upperShriekStdIsoFNewShriekNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsSeparated f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS)
    (j : CompactificationOf (Over.mk f)) :
    haveI := hq.source_noetherian
    UpperShriekDuality.upperShriekStd (ftsHomSelf (isShriekable_of_isSeparated hpe hp hq)) j ≅
      (plusCoh Y).ι ⋙ fNewShriekStd f (stdComplex nagataCompactification 𝒦X)
        (stdComplex nagataCompactification 𝒦Y) :=
  haveI := hq.source_noetherian
  UpperShriekDuality.upperShriekStdCompactificationIso
      (ftsHomSelf (isShriekable_of_isSeparated hpe hp hq)) j
      (nagataCompactification f (isShriekable_of_isSeparated hpe hp hq)) ≪≫
    upperShriekStdIsoFNewShriek nagataCompactification hpe hωS
      (isShriekable_of_isSeparated hpe hp hq) 𝒦X 𝒦Y

end NormalizedOnOpens

end Stacks.Duality

end
