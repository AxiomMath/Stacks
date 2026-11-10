module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiOpens
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiRingedSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteAssociatedModule
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedOfEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE

/-!
# Zariski cohomology of a quasi-coherent module is its cohomology on the small Zariski site

Let `S` be a scheme in a big Zariski site `B`, let `F` be a quasi-coherent `𝒪_S`-module and let
`Fᵃ` be the associated module of [Stacks, Tag 03DU] (4) at `τ = Zariski`, a sheaf of modules on
the small Zariski site `S_Zar` of [Stacks, Tag 020T] (2).  This file proves the small Zariski
half of clause (2) of [Stacks, Tag 03DW]:

  `H^p(V, ℱ) ≅ H^p(V_Zar, Fᵃ)`

for every open `V` of `S` and every degree `p`, and in particular, at `V = ⊤`,

  `H^p(S, ℱ) ≅ H^p(S_Zar, Fᵃ)`.

## Main definitions

* `AlgebraicGeometry.opensToSmallZariski`: the open subscheme `V.ι : V ⟶ S` read as an object
  of the small Zariski site, as a functor `S.Opens ⥤ S_Zar`.
* `AlgebraicGeometry.smallZariskiSectionsUnitIso`: the degree-zero half, `ℱ ≅ ε_* Fᵃ`.
* `AlgebraicGeometry.smallZariskiQuasiCoherentCohomologyIso`: the comparison over an arbitrary
  open of `S`.
* `AlgebraicGeometry.smallZariskiQuasiCoherentGlobalCohomologyIso`: **the small Zariski half of
  clause (2) of [Stacks, Tag 03DW]**, over the whole scheme, which is how the source states it.

## Main results

* `AlgebraicGeometry.opensToSmallZariski_isEquivalence` and
  `AlgebraicGeometry.opensToSmallZariski_isContinuous`: the functor is an equivalence of sites.
* `AlgebraicGeometry.isTerminal_opensToSmallZariski_top`: `⊤` goes to a final object of
  `S_Zar`, so the right-hand side below is the cohomology of the site itself.
* `AlgebraicGeometry.isZero_rightDerived_smallZariskiPushforward`: the higher direct images of
  `Fᵃ` along `ε : S_Zar ⟶ S_Zar(space)` vanish.

## Implementation notes

The shape of the argument is that of the two companion files
`SmallEtaleQuasiCoherentCohomology.lean`
and
`BigSiteQuasiCoherentCohomology.lean`
of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/CechComparison/`, which carry the other halves of
[Stacks, Tag 03DW]: the Leray collapse
`Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` along a continuous functor out of
the opens of `S`, with the vanishing of the higher direct images supplied separately and the
degree-zero identification `ℱ ≅ ε_* Fᵃ` composed in front of it.

What is special to the Zariski case is that the comparison functor is an *equivalence* of
sites: `AlgebraicGeometry.smallZariskiToOpens` takes the open image of an object of `S_Zar` and
is an equivalence onto `S.Opens` matching the two topologies, by
`AlgebraicGeometry.smallZariskiToOpens_isEquivalence_and_isDenseSubsite` ([Stacks, Tag 020X]).
Consequently the two inputs of the collapse are cheap rather than deep:

* the vanishing of the higher direct images is
  `CategoryTheory.Functor.isZero_rightDerived_of_isEquivalence` — restriction along an
  equivalence of sites is an equivalence of the abelian sheaf categories, hence exact, hence its
  own derived functor — and no affine acyclicity is needed, unlike on the big sites and on the
  small étale site;
* the degree-zero identification is the same `AlgebraicGeometry.isIso_pullbackSectionHom_ι`
  that the small étale file uses, a statement about an arbitrary module on an arbitrary scheme
  which sees no site.

The functor `AlgebraicGeometry.opensToSmallZariski` is built explicitly, sending `V` to
`Over.mk V.ι`, rather than taken to be the inverse equivalence of
`AlgebraicGeometry.smallZariskiToOpens`.  Only the explicit one makes the sections of `Fᵃ` over
its values be `Γ(V, V.ι^* F)` on the nose, which is what
`AlgebraicGeometry.isIso_pullbackSectionHom_ι` is about; the inverse equivalence reaches an
object chosen by essential surjectivity, whose structure morphism is merely *some* open
immersion with image `V`.  Continuity and the equivalence of the sheaf categories are then
transported from the inverse along
`AlgebraicGeometry.opensToSmallZariskiIsoInverse`, through
`CategoryTheory.Functor.isContinuous_of_iso` and
`CategoryTheory.Functor.sheafPushforwardContinuousIso`.

Cohomology is `CategoryTheory.Sheaf.H'`, `Ext` out of the free abelian sheaf on the Yoneda
presheaf of the object, at `Ext` universe `u` on both sides, exactly as in the two companion
files.  On the Zariski side the `Ext` universe and enough injectives are the theorems
`Stacks.Topology.hasExt_sheafOpens` and `Stacks.Topology.enoughInjectives_sheafOpens`; on the
small Zariski side they are
`Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite` and
`..._enoughInjectives_essentiallySmallSite`, the site being essentially small at the universe of
its morphisms because it is equivalent to `S.Opens`
(`AlgebraicGeometry.essentiallySmall_smallZariski`).  No instance priority has to be flipped,
unlike on the small étale site.

**The `@[stacks 03DW]` attribute is attached to the `V = ⊤` form below.**  The tag's clause (2)
is the chain `H^q(S, ℱ) = H^q(S_Zar, Fᵃ) = H^q(S_étale, Fᵃ)`, and its covering set is one
declaration per link: this file for the small Zariski link and
`AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` for the small étale one.
Clause (1) is `AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso`.  No `@[stacks 03P2]`
attribute is attached: [Stacks, Tag 03P2] lets `𝒞` be a big `τ`-site or `S_étale` and does not
include `S_Zar`.

The small Zariski site of this development is indexed by a chosen big Zariski site `B` with
`S` below its cutoff, as [Stacks, Tag 020T] (2) defines it and as
`AlgebraicGeometry.SmallZariski.associatedModuleOfSections`, the `Fᵃ` of [Stacks, Tag 03DU] (4)
at `τ = Zariski`, already is; `B` and `hS` are the datum of the site and not hypotheses on the
statement.

## References

* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The opens of `S` as objects of the small Zariski site -/

/-- An open `V` of `S` read as an object of the small Zariski site of `S`, namely the open
immersion `V.ι : V ⟶ S`. -/
public def opensToSmallZariskiObj (V : S.Opens) : SmallZariski B S hS := by
  let V₀ : B.Schemes := ⟨(V : Scheme), (Scheme.size_coe_opens_le S V).trans_lt hS⟩
  let S₀ : B.Schemes := ⟨S, hS⟩
  let i : V₀ ⟶ S₀ := ObjectProperty.homMk V.ι
  refine ⟨Over.mk i, ?_⟩
  change IsOpenImmersion (B.inclusion.map i)
  simpa [i] using (inferInstance : IsOpenImmersion V.ι)

/-- The structure morphism of `AlgebraicGeometry.opensToSmallZariskiObj` is the inclusion of the
open subscheme.  This is what makes the sections of `Fᵃ` over it be `Γ(V, V.ι^* F)` on the
nose. -/
public theorem inclusion_map_opensToSmallZariskiObj_hom (V : S.Opens) :
    B.inclusion.map (opensToSmallZariskiObj B S hS V).obj.hom = V.ι := rfl

/-- **The opens of `S` as a site over the small Zariski site of `S`.**  An open `V` is sent to
the open immersion `V.ι : V ⟶ S`, and an inclusion of opens to the corresponding inclusion of
open subschemes `AlgebraicGeometry.Scheme.homOfLE`. -/
public def opensToSmallZariski : S.Opens ⥤ SmallZariski B S hS where
  obj V := opensToSmallZariskiObj B S hS V
  map {_ _} h := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk (S.homOfLE h.le))
    (by apply ObjectProperty.hom_ext; exact S.homOfLE_ι h.le))
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp only [Scheme.homOfLE_rfl, ObjectProperty.homMk_hom, Over.homMk_left,
      ObjectProperty.FullSubcategory.id_hom, Over.id_left]
    rfl
  map_comp {_ _ _} f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact (S.homOfLE_homOfLE f.le g.le).symm

/-- The open image of `AlgebraicGeometry.opensToSmallZariski` at `V` is `V` again. -/
public theorem smallZariskiToOpens_opensToSmallZariski (V : S.Opens) :
    (smallZariskiToOpens B S hS).obj ((opensToSmallZariski B S hS).obj V) = V :=
  Scheme.Opens.opensRange_ι V

/-- `AlgebraicGeometry.opensToSmallZariski` is a section of the open-image functor. -/
public def opensToSmallZariskiCompIso :
    opensToSmallZariski B S hS ⋙ smallZariskiToOpens B S hS ≅ 𝟭 S.Opens :=
  NatIso.ofComponents (fun V => eqToIso (smallZariskiToOpens_opensToSmallZariski B S hS V))
    (fun _ => Subsingleton.elim _ _)

/-- **`AlgebraicGeometry.opensToSmallZariski` is the inverse of the open-image equivalence.**
This is how continuity and the equivalence of the abelian sheaf categories are transported to
it from `AlgebraicGeometry.smallZariskiSiteEquiv`. -/
public def opensToSmallZariskiIsoInverse :
    opensToSmallZariski B S hS ≅ (smallZariskiSiteEquiv B S hS).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (smallZariskiSiteEquiv B S hS).unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (opensToSmallZariskiCompIso B S hS) _ ≪≫
          Functor.leftUnitor _

/-- The opens of `S` are the small Zariski site of `S`. -/
public instance opensToSmallZariski_isEquivalence :
    (opensToSmallZariski B S hS).IsEquivalence :=
  Functor.isEquivalence_of_iso (opensToSmallZariskiIsoInverse B S hS).symm

/-- `AlgebraicGeometry.opensToSmallZariski` is continuous for the Zariski topology on the opens
of `S` and the topology of the small Zariski site. -/
public instance opensToSmallZariski_isContinuous :
    (opensToSmallZariski B S hS).IsContinuous (Opens.grothendieckTopology S.carrier)
      (SmallZariski.topology B S hS) :=
  Functor.isContinuous_of_iso (opensToSmallZariskiIsoInverse B S hS).symm _ _

-- The instance `AlgebraicGeometry.essentiallySmall_smallZariski` is imported from
-- `StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiRingedSiteHom`, which
-- declares it.

/-- **`S` itself is a final object of its small Zariski site**, reached by `⊤`.  This is what
makes the right-hand side of the comparison below the cohomology of the site. -/
public def isTerminal_opensToSmallZariski_top :
    IsTerminal ((opensToSmallZariski B S hS).obj (⊤ : S.Opens)) :=
  (IsTerminal.ofUniqueHom (fun (_ : S.Opens) => homOfLE le_top)
    (fun _ _ => Subsingleton.elim _ _)).isTerminalObj (opensToSmallZariski B S hS) _

/-! ### Restriction of abelian sheaves along the comparison -/

/-- The presenting functor of the small Zariski site as a site of schemes over `S`.  This is the
functor along which `AlgebraicGeometry.SmallZariski.associatedModuleOfSections` is defined. -/
public abbrev smallZariskiToOver : SmallZariski B S hS ⥤ Over S :=
  SmallZariski.inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion

/-- Abelian sheaves on the small Zariski site have a sheafification, the site being equivalent
to the opens of `S`. -/
public instance hasSheafify_smallZariskiTopology :
    HasSheafify (SmallZariski.topology B S hS) AddCommGrpCat.{u} :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence (Opens.grothendieckTopology S.carrier)
    (SmallZariski.topology B S hS) (smallZariskiSiteEquiv B S hS).inverse
    (A := AddCommGrpCat.{u})

/-- **The direct image `ε_*` of abelian sheaves along `ε : S_Zar ⟶ S_Zar(space)`**, the
restriction of a sheaf on the small Zariski site to the opens of `S`. -/
public abbrev smallZariskiPushforward :
    Sheaf (SmallZariski.topology B S hS) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u} :=
  (opensToSmallZariski B S hS).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology S.carrier) (SmallZariski.topology B S hS)

/-- **Restriction to the opens of `S` is an equivalence of abelian sheaf categories.**  This is
the equivalence of [Stacks, Tag 020X], transported from the inverse of the open-image
equivalence along `AlgebraicGeometry.opensToSmallZariskiIsoInverse`. -/
public instance smallZariskiPushforward_isEquivalence :
    (smallZariskiPushforward B S hS).IsEquivalence :=
  Functor.isEquivalence_of_iso
    (Functor.sheafPushforwardContinuousIso (opensToSmallZariskiIsoInverse B S hS).symm
      AddCommGrpCat.{u} (Opens.grothendieckTopology S.carrier) (SmallZariski.topology B S hS))

variable (F : S.Modules) [F.IsQuasicoherent]

/-- **`Fᵃ` as an abelian sheaf on the small Zariski site of `S`**: the associated module of
[Stacks, Tag 03DU] (4) at `τ = Zariski` with its module structure forgotten.  Its value at an
object `T ⟶ S` of the site is `Γ(T, T.hom^* F)`. -/
public abbrev smallZariskiAssociatedSheaf :
    Sheaf (SmallZariski.topology B S hS) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (SmallZariski.structureSheaf B S hS)).obj
    (SmallZariski.associatedModuleOfSections B S hS F)

/-- **Pulling sections back, as a morphism of abelian presheaves on the opens of `S`.**  A
section of `F` over an open `V` pulls back to a section of `V.ι^* F` over all of the open
subscheme `V`, naturally in `V`.

Naturality is the two lemmas `AlgebraicGeometry.pullbackSectionHom_map` — restricting the
section before pulling it back changes nothing — and
`AlgebraicGeometry.pullbackSectionsMap_pullbackSectionHom` — the presheaf of
[Stacks, Tag 03DS] carries pullbacks of sections to pullbacks of sections. -/
public def smallZariskiSectionsUnit :
    Scheme.Modules.presheaf F ⟶
      (opensToSmallZariski B S hS).op ⋙ (smallZariskiToOver B S hS).op ⋙
        quasiCoherentPresheafFunctor S F where
  app V := pullbackSectionHom (Scheme.Opens.ι V.unop) F V.unop ⊤
    (Scheme.Opens.top_le_ι_preimage le_rfl)
  naturality {U V} h := by
    ext a
    have hUV : V.unop ≤ U.unop := leOfHom h.unop
    exact (pullbackSectionHom_map (Scheme.Opens.ι V.unop) F U.unop V.unop hUV ⊤
      (Scheme.Opens.top_le_ι_preimage le_rfl) (Scheme.Opens.top_le_ι_preimage hUV) a).trans
      (pullbackSectionsMap_pullbackSectionHom F
      ((smallZariskiToOver B S hS).map ((opensToSmallZariski B S hS).map h.unop))
      U.unop (Scheme.Opens.top_le_ι_preimage le_rfl)
      (Scheme.Opens.top_le_ι_preimage hUV) a).symm

/-- **Pulling sections back to the open subschemes is an isomorphism.**  Each component is the
map of `AlgebraicGeometry.isIso_pullbackSectionHom_ι`, a statement about an arbitrary module on
an arbitrary scheme which sees no site. -/
public theorem isIso_smallZariskiSectionsUnit : IsIso (smallZariskiSectionsUnit B S hS F) :=
  (NatTrans.isIso_iff_isIso_app _).mpr fun V => isIso_pullbackSectionHom_ι F V.unop

/-- **`ℱ ≅ ε_* Fᵃ`, the degree-zero half of the small Zariski case of [Stacks, Tag 03DW] (2).**
The abelian sheaf on the Zariski site of `S` underlying a quasi-coherent module `F` agrees with
the restriction to the opens of `S` of the associated module `Fᵃ` on the small Zariski site.

The two underlying presheaves agree by `rfl` — restriction along a continuous functor is
restriction of sections — so this is `AlgebraicGeometry.isIso_smallZariskiSectionsUnit` carried
across `CategoryTheory.fullyFaithfulSheafToPresheaf`. -/
public def smallZariskiSectionsUnitIso :
    (SheafOfModules.toSheaf S.ringCatSheaf).obj F ≅
      (smallZariskiPushforward B S hS).obj (smallZariskiAssociatedSheaf B S hS F) :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology S.carrier)
      AddCommGrpCat.{u}).preimageIso
    (@asIso _ _ _ _ (smallZariskiSectionsUnit B S hS F)
      (isIso_smallZariskiSectionsUnit B S hS F))

/-! ### The comparison of cohomology -/

-- The Zariski side of the collapse asks for an `Ext` universe and enough injectives in the
-- coefficients themselves; both are available at any coefficient universe dominating the space,
-- but only as theorems.  The small Zariski side is essentially small at `u`, which supplies the
-- same two there.
attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

/-- **The higher direct images of `Fᵃ` along `ε : S_Zar ⟶ S_Zar(space)` vanish.**  This is the
hypothesis of the Leray collapse below.  Restriction along `ε` is an equivalence of abelian
sheaf categories, hence exact, so it is its own derived functor:
`CategoryTheory.Functor.isZero_rightDerived_of_isEquivalence`. -/
public theorem isZero_rightDerived_smallZariskiPushforward (p : ℕ) (hp : 0 < p) :
    IsZero (((smallZariskiPushforward B S hS).rightDerived p).obj
      (smallZariskiAssociatedSheaf B S hS F)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  exact Functor.isZero_rightDerived_of_isEquivalence _ _ m

/-- **The cohomology of `Fᵃ` over an open of `S` collapses onto Zariski cohomology of `ℱ`.**
For a quasi-coherent module `F` on `S`, an open `V` of `S` and a degree `p`,

  `H^p(V, ℱ) ≅ H^p(V_Zar, Fᵃ)`,

where the right-hand side is the cohomology on the small Zariski site of `S` of the associated
module `Fᵃ`, taken over the object `V.ι : V ⟶ S`.

This is `Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso` for the continuous functor
`AlgebraicGeometry.opensToSmallZariski`, whose hypothesis is discharged by
`AlgebraicGeometry.isZero_rightDerived_smallZariskiPushforward`, read on the Zariski side
through `AlgebraicGeometry.smallZariskiSectionsUnitIso`.

This is the generalisation to an arbitrary open of `S` of the small Zariski half of clause (2)
of [Stacks, Tag 03DW], and carries no attribute: the tag's statement is the one at `S` itself,
which is `AlgebraicGeometry.smallZariskiQuasiCoherentGlobalCohomologyIso` below. -/
public def smallZariskiQuasiCoherentCohomologyIso (p : ℕ) (V : S.Opens) :
    Sheaf.H' ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p V ≅
      Sheaf.H' (smallZariskiAssociatedSheaf B S hS F) p
        ((opensToSmallZariski B S hS).obj V) :=
  ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology S.carrier) p).mapIso
      (smallZariskiSectionsUnitIso B S hS F)).app (op V) ≪≫
    Stacks.Cohomology.BiggerSite.sheafCohomologyPushforwardIso
      (Opens.grothendieckTopology S.carrier) (SmallZariski.topology B S hS)
      (opensToSmallZariski B S hS) (smallZariskiAssociatedSheaf B S hS F) V p
      (fun q hq _ ↦ isZero_rightDerived_smallZariskiPushforward B S hS F q hq)

/-- **Zariski cohomology of a quasi-coherent module agrees with the cohomology of its associated
module on the small Zariski site**: for a quasi-coherent module `F` on a scheme `S` and a degree
`p`,

  `H^p(S, ℱ) ≅ H^p(S_Zar, Fᵃ)`.

This is `AlgebraicGeometry.smallZariskiQuasiCoherentCohomologyIso` at the whole scheme.  The
object it is taken over on the right, `(opensToSmallZariski B S hS).obj ⊤`, is a final object of
the small Zariski site by `AlgebraicGeometry.isTerminal_opensToSmallZariski_top`, so the
right-hand side is the cohomology of `S_Zar` itself.

**This is the small Zariski half of clause (2) of [Stacks, Tag 03DW]**, in every degree.
Together with `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso`, the small étale
half, it is the covering set of that clause. -/
@[stacks 03DW "clause (2), the small ZARISKI half H^q(S, F) = H^q(S_Zar, Fᵃ), in EVERY degree \
q.  S_Zar is the small Zariski site of Tag 020T (2) and Fᵃ the associated module of Tag 03DU \
(4) at τ = Zariski, SmallZariski.associatedModuleOfSections.  The object the right-hand side is \
taken over, (opensToSmallZariski B S hS).obj ⊤, is a final object of the site by \
isTerminal_opensToSmallZariski_top, so that side is the cohomology of S_Zar itself.  The other \
half of clause (2), H^q(S, F) = H^q(S_étale, Fᵃ), is \
smallEtaleQuasiCoherentGlobalCohomologyIso; clause (1) is \
bigOverQuasiCoherentGlobalCohomologyIso.  No 03P2 attribute: that tag lets 𝒞 be a big τ-site \
or S_étale and does not include S_Zar"]
public def smallZariskiQuasiCoherentGlobalCohomologyIso (p : ℕ) :
    Sheaf.H' ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p ⊤ ≅
      Sheaf.H' (smallZariskiAssociatedSheaf B S hS F) p
        ((opensToSmallZariski B S hS).obj ⊤) :=
  smallZariskiQuasiCoherentCohomologyIso B S hS F p ⊤

end AlgebraicGeometry

end
