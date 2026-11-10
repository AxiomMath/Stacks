module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredTensorHypotheses
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFilteredColimitsSections
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0GQZ: Hom out of a finitely presented module and filtered colimits on a stack

Let `𝒳` be a category fibred in groupoids over the big fppf category of a scheme `S`, give its
total category the fppf topology of Stacks 06TP and the structure sheaf of Stacks 06TV, let `𝒢` be
an `𝒪_𝒳`-module and let `i ↦ ℱ_i` be a filtered system of `𝒪_𝒳`-modules. Stacks 0GQZ asserts, for
`𝒳` a quasi-compact and quasi-separated algebraic stack and `𝒢` of finite presentation,

`colim_i Hom_𝒳(𝒢, ℱ_i) = Hom_𝒳(𝒢, colim_i ℱ_i)`,

and the same for filtered colimits taken in `QCoh(𝒪_𝒳)`.

The proof is the one of the source: the equality is the case of Stacks 0GN0 for the fppf ringed
site of `𝒳`, whose site hypothesis — the condition of Stacks 0GMR part (4) — the source checks for
the objects of the site lying over affine schemes through Stacks 0GMS case (2).

## The universe gap, and how it is bridged

Stacks 0GN0 and its input Stacks 0GMZ are available only for an
`AlgebraicGeometry.RingedSite.{t, t, t}`, whereas `AlgebraicGeometry.FibredSite.ringedSite`
applied to a category fibred in groupoids over the big fppf category of `S` is an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`: its objects lie in `Type (u + 1)` and its morphisms
in `Type u`. As
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleEquiUniverseModel.lean` records for the small
étale site of an algebraic space, relaxing the universes in the *statements* of Stacks 0GMZ and
Stacks 0GN0 cannot reach those modules however the hypotheses are arranged: the sections of the
internal Hom sheaf on a site with objects in `Type u₁` and morphisms in `Type v₁` lie in
`Type (max u₁ v₁ …)`, so internal Hom is an endofunctor of the modules only at module universes
at least `max u₁ v₁`, which is `u + 1` here, while the modules of the stacks development have
sections in `Type u`.

The remedy is the same as there: pass to a model of the site whose objects and morphisms both lie
in `Type u`. The first half of this file builds that model for an *arbitrary* site which is
essentially small in the universe of its structure sheaf, and transports Stacks 0GN0 back across
it; the second half instantiates it at the fppf site of a category fibred in groupoids. Essential
smallness of that site is an instance hypothesis throughout: it holds as soon as the
size-bounded category of schemes is essentially small and every fibre of `𝒳` is, by
`AlgebraicGeometry.Stack.essentiallySmall_obj`, and the second of those is not formal.

## What is proved and what is assumed

The site hypothesis of Stacks 0GN0 is *not* discharged here. Conditions (2)(a), (2)(b) and (2)(c)
of Stacks 0GMS are available for the fppf site of a quasi-compact algebraic stack which is
quasi-separated over a quasi-separated base — they are
`AlgebraicGeometry.Stack.exists_isAffineObject_isLocallySurjective_terminal_from`,
`AlgebraicGeometry.Stack.hasFiniteCoverRefinementsFrom_fppfTopology` and
`AlgebraicGeometry.Stack.exists_fin_affineObjects_isLocallySurjective_prodLift` — but they are
statements about sheaves of sets at the canonical sheaf universe `Type (u + 1)` of that site,
whereas Stacks 0GN0 consumes the corresponding statement at `Type u` for the model. Sheaf-level
conditions do not transport along an equivalence of sites across a universe gap (see the module
docstring of `StacksFrontier/CategoryTheory/Sites/QuasiCompact/CoveringSetTransport.lean`), so
checking them on the model is separate work, performed for the small étale site of an algebraic
space in `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModelCoveringSet.lean` and not performed
here. It is carried as the hypothesis `hX` below.

Finite presentation of `𝒢`, by contrast, *is* a hypothesis about `𝒢` on the fppf site itself, and
is carried across to the model by
`AlgebraicGeometry.FibredSite.isFinitePresentation_modulesEquivFppfModelModules`. It is Mathlib's
predicate `SheafOfModules.IsFinitePresentation`, which is the one Stacks 0GN0 is stated over; the
site predicate `SheafOfModules.IsFinitePresentationOnSite` of Stacks 03DL, in which the stacks
development states finite presentation elsewhere, is not bridged to it anywhere in the tree, so
the two clauses below are about the Mathlib predicate only.

Accordingly neither quasi-compactness nor quasi-separatedness of `𝒳` appears below, and `𝒳` is
not assumed to be an algebraic stack: those hypotheses of the source enter only through `hX`,
and no hypothesis is carried that is not used. This follows the shape of
`AlgebraicGeometry.Stack.isIso_colimit_post_rightDerived_globalSections_fppf`, the companion
statement for cohomology.

## Main definitions

* `Stacks.SheafOfModules.SmallModelSite.ringedSite`: a site essentially small in the universe of
  its structure sheaf, transported to a model in that universe, as an
  `AlgebraicGeometry.RingedSite.{u, u, u}`.
* `Stacks.SheafOfModules.SmallModelSite.modulesEquivalence` and
  `AlgebraicGeometry.FibredSite.modulesEquivFppfModelModules`: the identification of the sheaves
  of modules on a site with the sheaves of modules on that model.

## Main results

* `Stacks.SheafOfModules.SmallModelSite`
  `.preservesColimitsOfShape_coyoneda_of_isFinitePresentation_model`: Stacks 0GN0 across the
  universe gap — `Hom_O(𝒢, -)` commutes with filtered colimits on a site which is merely
  essentially small in the universe of its structure sheaf.
* `Stacks.SheafOfModules.SmallModelSite.isFinitePresentation_modulesEquivalence` and
  `AlgebraicGeometry.FibredSite.isFinitePresentation_modulesEquivFppfModelModules`: finite
  presentation is carried to the model.
* `AlgebraicGeometry.FibredSite.isIso_colimit_post_hom_of_isFinitePresentation`:
  **Stacks 0GQZ for all modules**, with `hX` carried.
* `AlgebraicGeometry.FibredSite.isIso_colimit_post_hom_quasicoherent_of_isFinitePresentation`:
  **Stacks 0GQZ for quasi-coherent modules**, with `hX` and the closure of quasi-coherence under
  the colimits at issue carried.

## Implementation notes

The generic half lives in this file rather than under `StacksFrontier/CategoryTheory/` because its
input, `Stacks.SheafOfModules.reindexEquivalence`, currently lives in the
algebraic-spaces tree. It is a generalisation of the bespoke
construction of `AlgebraicGeometry.Space.smallEtaleModelRingedSite`, which is left untouched.

The index category of the colimit is small in the module universe, `K : Type u` with
`Category.{u} K`, which is what Stacks 0GMZ and the library's form of Stacks 0GN0 ask for; the
source quantifies over an arbitrary directed set.

The two `HasColimit` hypotheses are instance binders rather than consequences: on the fppf site of
a category fibred in groupoids with no smallness hypothesis the module category is not known to
have the colimits in question, and the comparison morphism `CategoryTheory.Limits.colimit.post`
is not even defined without them.

The quasi-coherent clause is deduced from the clause for all modules through the full and faithful
inclusion of the quasi-coherent modules: `Hom` out of a fixed object of a full subcategory is
`Hom` out of its image, so `Hom(𝒢, -)` commutes with a colimit of quasi-coherent modules as soon
as the inclusion does and `Hom(𝒢, -)` commutes with its image. That the inclusion preserves the
colimit — the colimit clause of Stacks 03M1 for the fppf site of a stack — is the carried
hypothesis; it is available for an algebraic space only conditionally, in
`AlgebraicGeometry.Space.isQuasicoherent_colimit_of_h03DX`, and not at all for a stack.

## References

* [Stacks Project, Tag 0GQZ](https://stacks.math.columbia.edu/tag/0GQZ)
* [Stacks Project, Tag 0GN0](https://stacks.math.columbia.edu/tag/0GN0)
* [Stacks Project, Tag 0GMZ](https://stacks.math.columbia.edu/tag/0GMZ)
* [Stacks Project, Tag 0GMR](https://stacks.math.columbia.edu/tag/0GMR)
* [Stacks Project, Tag 0GMS](https://stacks.math.columbia.edu/tag/0GMS)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 07U7](https://stacks.math.columbia.edu/tag/07U7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.SheafOfModules.SmallModelSite

/-! ### An equi-universe model of a site essentially small in its sheaf universe -/

universe u u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{u} C]

/-- The equivalence between a model of `C` in the universe `u` and `C` itself, in the direction
in which the model is the source. -/
noncomputable def equivalence : SmallModel.{u} C ≌ C where
  functor := (equivSmallModel.{u} C).inverse
  inverse := (equivSmallModel.{u} C).functor
  unitIso := (equivSmallModel.{u} C).counitIso.symm
  counitIso := (equivSmallModel.{u} C).unitIso.symm
  functor_unitIso_comp _ := by simp

variable (J : GrothendieckTopology C)

/-- The topology on a model of `C` in the universe `u` induced from `J`. -/
noncomputable abbrev topology : GrothendieckTopology (SmallModel.{u} C) :=
  (equivSmallModel.{u} C).inverse.inducedTopology J

/-- The functor of the model equivalence is continuous from the induced topology to `J`. -/
instance functor_isContinuous :
    (equivalence.{u} (C := C)).functor.IsContinuous (topology.{u} J) J :=
  inferInstanceAs ((equivSmallModel.{u} C).inverse.IsContinuous _ _)

/-- The inverse of the model equivalence is continuous from `J` to the induced topology. -/
instance inverse_isContinuous :
    (equivalence.{u} (C := C)).inverse.IsContinuous J (topology.{u} J) :=
  inferInstanceAs ((equivSmallModel.{u} C).functor.IsContinuous _ _)

/-- The inverse of the model equivalence exhibits `C` as a dense subsite of its model: the
topology of the model is the one induced along the equivalence. This is the single instance from
which Mathlib derives continuity, cocontinuity and cover-density of both functors. -/
instance inverse_isDenseSubsite :
    (equivalence.{u} (C := C)).inverse.IsDenseSubsite J (topology.{u} J) :=
  inferInstanceAs ((equivSmallModel.{u} C).functor.IsDenseSubsite _ _)

/-- The functor of the model equivalence exhibits the model as a dense subsite of `C`. -/
instance functor_isDenseSubsite :
    (equivalence.{u} (C := C)).functor.IsDenseSubsite (topology.{u} J) J :=
  inferInstanceAs ((equivSmallModel.{u} C).inverse.IsDenseSubsite _ _)

variable (O : Sheaf J CommRingCat.{u})

/-- **The equi-universe model of a ringed site `(C, J, O)` whose underlying category is
essentially small in the universe of `O`**: the model site with the direct image of the structure
sheaf, an `AlgebraicGeometry.RingedSite` whose objects, morphisms and sections all lie in
`Type u`. -/
noncomputable def ringedSite : RingedSite.{u, u, u} where
  C := SmallModel.{u} C
  J := topology.{u} J
  O := ((equivalence.{u} (C := C)).functor.sheafPushforwardContinuous
    CommRingCat.{u} (topology.{u} J) J).obj O

/-- Continuity of the model equivalence, restated for the topology of
`Stacks.SheafOfModules.SmallModelSite.ringedSite`, which instance search does not unfold. -/
instance ringedSite_functor_isContinuous :
    (equivalence.{u} (C := C)).functor.IsContinuous (ringedSite.{u} J O).J J :=
  functor_isContinuous.{u} J

/-- Continuity of the inverse of the model equivalence, restated for the topology of
`Stacks.SheafOfModules.SmallModelSite.ringedSite`. -/
instance ringedSite_inverse_isContinuous :
    (equivalence.{u} (C := C)).inverse.IsContinuous J (ringedSite.{u} J O).J :=
  inverse_isContinuous.{u} J

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The sheaf of rings of the model is, on the nose, the direct image of the sheaf of rings of
the given site. -/
theorem ringSheaf_ringedSite :
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := (ringedSite.{u} J O).J)) (ringedSite.{u} J O).O =
      Stacks.SheafOfModules.reindexRing (topology.{u} J) (equivalence.{u} (C := C))
        (Tensor.ringSheaf O) :=
  rfl

/-- **The sheaves of modules on a site are the sheaves of modules on its equi-universe model.**
Reindexing along the model equivalence, which is an equivalence of the two categories of sheaves
of modules even though their hom types lie in different universes. -/
noncomputable def modulesEquivalence :
    _root_.SheafOfModules.{u} (Tensor.ringSheaf O) ≌
      _root_.SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (ringedSite.{u} J O).J))
          (ringedSite.{u} J O).O) :=
  Stacks.SheafOfModules.reindexEquivalence (equivalence.{u} (C := C))
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O)

/-- The model has fibre products, transported from the given site along the model
equivalence. -/
instance hasPullbacks_smallModel [HasPullbacks C] : HasPullbacks (SmallModel.{u} C) :=
  Adjunction.hasLimitsOfShape_of_equivalence (equivalence.{u} (C := C)).functor

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Finite presentation is carried to the equi-universe model.** If a sheaf of modules on the
given site is of finite presentation, so is the sheaf of modules it becomes on
`Stacks.SheafOfModules.SmallModelSite.ringedSite`.

The three site-level inputs are explicit arguments rather than instance binders, so that a
consumer can hand over the instances of its own development: the underlying category of a site
is reachable both directly and as a projection, and instance search sees only one spelling at a
time. On the model side they are found by search, the model being a small category. -/
theorem isFinitePresentation_modulesEquivalence (hpull : HasPullbacks C)
    (hsheafify : ∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u})
    (hlocBij : ∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u})
    (G : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)) (hG : G.IsFinitePresentation) :
    ((modulesEquivalence.{u} J O).functor.obj G).IsFinitePresentation :=
  let := hpull
  let := hsheafify
  let := hlocBij
  let := hG
  SiteTransport.isFinitePresentation_modulesEquivalence (topology.{u} J)
    (equivalence.{u} (C := C)) G

universe k

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **`Hom_O(𝒢, -)` commutes with colimits of a given shape as soon as its transport to the
equi-universe model does.** The two hom types lie in different universes, so the transport
inserts a universe lift; both it and the functor of the equivalence commute with colimits. -/
theorem preservesColimitsOfShape_coyoneda_of_model
    (G : _root_.SheafOfModules.{u} (Tensor.ringSheaf O)) (K : Type k) [Category.{k} K]
    [PreservesColimitsOfShape K
      (coyoneda.obj (Opposite.op ((modulesEquivalence.{u} J O).functor.obj G)))] :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G)) :=
  SiteTransport.preservesColimitsOfShape_coyoneda_of_equivalence.{max u u₁, u, _, _, k}
    (modulesEquivalence.{u} J O) G K

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Stacks 0GN0 across the universe gap.** On a site whose underlying category is essentially
small in the universe `u` of its structure sheaf — not necessarily with its objects and its
morphisms both in `Type u`, which is the shape Stacks 0GN0 is stated in — `Hom_O(𝒢, -)` commutes
with filtered colimits of `O`-modules.

Two hypotheses are carried, both of them about the model
`Stacks.SheafOfModules.SmallModelSite.ringedSite` rather than about the given site: `hG`, that
the transport of `𝒢` to the model is of finite presentation, and `hX`, the condition of
Stacks 0GMR part (4) for the model, which Stacks 0GMS records sufficient conditions for and which
cannot be dropped — already for `𝒢 = O` the conclusion is the assertion that global sections
commute with the colimit. -/
theorem preservesColimitsOfShape_coyoneda_of_isFinitePresentation_model
    (G : _root_.SheafOfModules.{u} (Tensor.ringSheaf O))
    (hG : ((modulesEquivalence.{u} J O).functor.obj G).IsFinitePresentation)
    (K : Type u) [Category.{u} K] [IsFiltered K]
    (hX : ∃ T : Set (Sheaf (topology.{u} J) (Type u)),
      (∀ H : Sheaf (topology.{u} J) (Type u),
          Sheaf.IsLocallySurjective (terminal.from H) →
            ∃ L ∈ T, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ T, Sheaf.IsQuasiCompact (L ⨯ L)) :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G)) :=
  have _ := hG
  have _ : PreservesColimitsOfShape K (coyoneda.obj
      (Opposite.op ((modulesEquivalence.{u} J O).functor.obj G))) :=
    InternalHom.coyoneda_preservesColimitsOfShape_of_isFinitePresentation
      (ringedSite.{u} J O) _ K hX
  preservesColimitsOfShape_coyoneda_of_model.{u} J O G K

end Stacks.SheafOfModules.SmallModelSite

/-! ### Hom out of a fixed object of a full subcategory -/

namespace CategoryTheory.ObjectProperty

universe v₂ u₂

variable {A : Type u₂} [Category.{v₂} A] (P : ObjectProperty A)

/-- **Hom out of an object of a full subcategory is Hom out of its image.** The full and faithful
inclusion of the subcategory, followed by `Hom` out of the image, is `Hom` out of the object. The
bijection on each component is `CategoryTheory.Functor.FullyFaithful.homEquiv` for
`CategoryTheory.ObjectProperty.fullyFaithfulι`. -/
def coyonedaIsoIotaCompCoyoneda (G : P.FullSubcategory) :
    coyoneda.obj (Opposite.op G) ≅ P.ι ⋙ coyoneda.obj (Opposite.op (P.ι.obj G)) :=
  NatIso.ofComponents
    (fun X => Equiv.toIso (P.fullyFaithfulι.homEquiv (X := G) (Y := X)))
    fun {X Y} g => by ext f; exact P.ι.map_comp f g

/-- **`Hom(𝒢, -)` on a full subcategory commutes with a shape of colimits** as soon as the
inclusion of the subcategory does and `Hom` out of the image of `𝒢` does. -/
theorem preservesColimitsOfShape_coyoneda_fullSubcategory (G : P.FullSubcategory)
    (K : Type*) [Category K] [hι : PreservesColimitsOfShape K P.ι]
    (hG : PreservesColimitsOfShape K (coyoneda.obj (Opposite.op (P.ι.obj G)))) :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G)) :=
  have _ := hG
  have _ : PreservesColimitsOfShape K
      (P.ι ⋙ coyoneda.obj (Opposite.op (P.ι.obj G))) := inferInstance
  preservesColimitsOfShape_of_natIso (P.coyonedaIsoIotaCompCoyoneda G).symm

end CategoryTheory.ObjectProperty

/-! ### Stacks 0GQZ -/

namespace AlgebraicGeometry.FibredSite

universe u v w

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The sheaf condition for `CommRingCat`-valued sheaves on an associated site of a category
fibred in groupoids is preserved by `forget₂ CommRingCat RingCat`, so the modules of the site are
modules over the sheaf of rings `AlgebraicGeometry.FibredSite.ringStructureSheafCore`. -/
theorem hasSheafCompose_associatedTopology (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    (BigFppfOver.associatedTopology B S hS p τ).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  RingedSite.hasSheafCompose_forget₂_ringCat (ringedSite B S hS p hp τ)

/-- The sheaf of rings over which the modules of an associated site are taken is the
`RingCat`-valued sheaf underlying its structure sheaf, on the nose. -/
theorem ringSheaf_eq_ringStructureSheafCore (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    letI := hasSheafCompose_associatedTopology B S hS p hp τ
    (Stacks.SheafOfModules.Tensor.ringSheaf (J := (BigFppfOver.associatedTopology B S hS p τ)))
        (structureSheaf B S hS p hp τ) =
      ringStructureSheafCore B S hS p hp τ :=
  rfl

variable [EssentiallySmall.{u} 𝒳]

/-- **The equi-universe model of the fppf ringed site of a category fibred in groupoids over the
big fppf category of `S`.** The fppf site has its objects in `Type (u + 1)` and its morphisms in
`Type u`; this is its transport to a model with both in `Type u`, which is the shape
Stacks 0GMZ and Stacks 0GN0 are stated in. -/
noncomputable abbrev fppfModelRingedSite (hp : p.IsFiberedInGroupoids) : RingedSite.{u, u, u} :=
  Stacks.SheafOfModules.SmallModelSite.ringedSite.{u}
    (BigFppfOver.associatedTopology B S hS p .fppf) (structureSheaf B S hS p hp .fppf)

/-- **The `𝒪_𝒳`-modules of a category fibred in groupoids are the sheaves of modules on the
equi-universe model of its fppf ringed site.** -/
noncomputable def modulesEquivFppfModelModules (hp : p.IsFiberedInGroupoids) :
    SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) ≌
      SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (fppfModelRingedSite B S hS p hp).J))
          (fppfModelRingedSite B S hS p hp).O) :=
  letI := hasSheafCompose_associatedTopology B S hS p hp .fppf
  Stacks.SheafOfModules.SmallModelSite.modulesEquivalence.{u} _
    (structureSheaf B S hS p hp .fppf)

open Stacks.SheafOfModules.SmallModelSite in
/-- **Stacks 0GN0 for the fppf site of a category fibred in groupoids, through its equi-universe
model.** `Hom_𝒳(𝒢, -)` commutes with filtered colimits of `𝒪_𝒳`-modules, granted that the
transport of `𝒢` to `AlgebraicGeometry.FibredSite.fppfModelRingedSite` is of finite presentation
and that the model satisfies the condition of Stacks 0GMR part (4).

This is the content of both clauses of Stacks 0GQZ below; see their docstrings and "What is
proved and what is assumed" in the module docstring for the status of the two hypotheses. -/
theorem preservesColimitsOfShape_coyoneda_fppf_of_isFinitePresentation_model
    (hp : p.IsFiberedInGroupoids)
    (G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hG : ((modulesEquivFppfModelModules B S hS p hp).functor.obj G).IsFinitePresentation)
    (K : Type u) [Category.{u} K] [IsFiltered K]
    (hX : ∃ T : Set (Sheaf (fppfModelRingedSite B S hS p hp).J (Type u)),
      (∀ H : Sheaf (fppfModelRingedSite B S hS p hp).J (Type u),
          Sheaf.IsLocallySurjective (terminal.from H) →
            ∃ L ∈ T, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ T, Sheaf.IsQuasiCompact (L ⨯ L)) :
    PreservesColimitsOfShape K (coyoneda.obj (Opposite.op G)) :=
  let := hasSheafCompose_associatedTopology B S hS p hp .fppf
  preservesColimitsOfShape_coyoneda_of_isFinitePresentation_model.{u}
    _ (structureSheaf B S hS p hp .fppf) G hG K hX

end General

/-! ### Stacks 0GQZ on the fppf site of an algebraic stack

The fppf site of a category fibred in groupoids over the big fppf category of `S` has its objects
in `Type (u + 1)` and its morphisms in `Type u`; that is the shape the fppf site of an algebraic
stack has, and the shape in which the sheafification hypotheses of
`SheafOfModules.IsFinitePresentation` are already available on the slices
(`AlgebraicGeometry.FibredSite.hasSheafify_associatedTopology_over` and
`AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_associatedTopology_over`). Both are pinned
as local instances below, which is what lets `𝒢` be assumed of finite presentation *on the fppf
site itself* rather than on the model. -/

section FppfSiteOfStack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS)

attribute [local instance] hasSheafify_associatedTopology_over
  wEqualsLocallyBijective_associatedTopology_over

/-- **Finite presentation is carried to the equi-universe model of the fppf site.** An
`𝒪_𝒳`-module of finite presentation stays of finite presentation on
`AlgebraicGeometry.FibredSite.fppfModelRingedSite`.

The three site-level inputs of
`Stacks.SheafOfModules.SmallModelSite.isFinitePresentation_modulesEquivalence` are supplied by
`AlgebraicGeometry.BigFppfOver.hasPullbacks_of_isFiberedInGroupoids` (Stacks 06WY),
`AlgebraicGeometry.FibredSite.hasSheafify_associatedTopology_over` and
`AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_associatedTopology_over`. -/
theorem isFinitePresentation_modulesEquivFppfModelModules (hp : p.IsFiberedInGroupoids)
    (G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hG : G.IsFinitePresentation) :
    ((modulesEquivFppfModelModules B S hS p hp).functor.obj G).IsFinitePresentation :=
  let := hasSheafCompose_associatedTopology B S hS p hp .fppf
  Stacks.SheafOfModules.SmallModelSite.isFinitePresentation_modulesEquivalence.{u}
    _ (structureSheaf B S hS p hp .fppf)
    (BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp)
    (hasSheafify_associatedTopology_over B S hS p .fppf)
    (wEqualsLocallyBijective_associatedTopology_over B S hS p .fppf) G hG

/-- **Stacks 0GQZ for all modules.** Let `𝒳` be a category fibred in groupoids over the big fppf
category of a scheme `S` contained in a big fppf site, with the fppf topology of Stacks 06TP and
the structure sheaf of Stacks 06TV, and assume its total category essentially small. Let `𝒢` be an
`𝒪_𝒳`-module of finite presentation and `D` a filtered system of `𝒪_𝒳`-modules. Then the canonical
comparison

`colim_i Hom_𝒳(𝒢, ℱ_i) ⟶ Hom_𝒳(𝒢, colim_i ℱ_i)`

is a bijection, granted the hypothesis `hX`.

`hX` is the condition of Stacks 0GMR part (4) for the equi-universe model
`AlgebraicGeometry.FibredSite.fppfModelRingedSite`, which is the site Stacks 0GN0 applies to and
which the fppf site itself — whose objects lie one universe above its morphisms — is not. It is
what the source checks for the objects of the site lying over affine schemes, through
Stacks 0GMS case (2), using quasi-compactness and quasi-separatedness of the algebraic stack.
Neither of those two hypotheses of the source appears here, and `𝒳` is not assumed to be an
algebraic stack: they enter only through `hX`.

Finite presentation is `SheafOfModules.IsFinitePresentation`, Mathlib's predicate, which is the
one Stacks 0GN0 is stated over; the site predicate
`SheafOfModules.IsFinitePresentationOnSite` of Stacks 03DL used elsewhere in the stacks
development is not bridged to it anywhere in the tree. See "What is proved and what is assumed"
in the module docstring. -/
@[stacks 0GQZ "all modules; condition 0GMR (4) for the equi-universe model of the fppf site is a \
hypothesis, so quasi-compactness, quasi-separatedness and algebraicity of the stack do not \
appear; finite presentation is Mathlib's, not 03DL's; the index category is small"]
theorem isIso_colimit_post_hom_of_isFinitePresentation (hp : p.IsFiberedInGroupoids)
    (G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hG : G.IsFinitePresentation)
    {K : Type u} [Category.{u} K] [IsFiltered K]
    (D : K ⥤ SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf))
    (hX : ∃ T : Set (Sheaf (fppfModelRingedSite B S hS p hp).J (Type u)),
      (∀ H : Sheaf (fppfModelRingedSite B S hS p hp).J (Type u),
          Sheaf.IsLocallySurjective (terminal.from H) →
            ∃ L ∈ T, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ T, Sheaf.IsQuasiCompact (L ⨯ L))
    [HasColimit D] [HasColimit (D ⋙ coyoneda.obj (Opposite.op G))] :
    IsIso (colimit.post D (coyoneda.obj (Opposite.op G))) :=
  have _ := preservesColimitsOfShape_coyoneda_fppf_of_isFinitePresentation_model
    B S hS p hp G (isFinitePresentation_modulesEquivFppfModelModules B S hS p hp G hG) K hX
  inferInstance

/-- **Stacks 0GQZ for quasi-coherent modules.** The same comparison, for a filtered colimit taken
in the category `QCoh(𝒪_𝒳)` of Stacks 06WG rather than in all `𝒪_𝒳`-modules.

Beyond the hypothesis `hX` of
`AlgebraicGeometry.FibredSite.isIso_colimit_post_hom_of_isFinitePresentation` this carries one
more: that the inclusion of the quasi-coherent modules into all modules preserves colimits of
shape `K`, which is the colimit clause of Stacks 03M1 for the fppf site of `𝒳`. That clause is
available for an algebraic space only conditionally, in
`AlgebraicGeometry.Space.isQuasicoherent_colimit_of_h03DX`, and is not available for a stack. -/
@[stacks 0GQZ "quasi-coherent modules; condition 0GMR (4) for the equi-universe model of the \
fppf site and preservation of the colimit by the inclusion of QCoh (the colimit clause of 03M1) \
are hypotheses, so quasi-compactness, quasi-separatedness and algebraicity of the stack do not \
appear; finite presentation is Mathlib's, not 03DL's; the index category is small"]
theorem isIso_colimit_post_hom_quasicoherent_of_isFinitePresentation
    (hp : p.IsFiberedInGroupoids) (G : quasicoherentModules.{u, u + 1, u, u} B S hS p hp)
    (hG : G.obj.IsFinitePresentation)
    {K : Type u} [Category.{u} K] [IsFiltered K]
    (D : K ⥤ quasicoherentModules.{u, u + 1, u, u} B S hS p hp)
    (hX : ∃ T : Set (Sheaf (fppfModelRingedSite B S hS p hp).J (Type u)),
      (∀ H : Sheaf (fppfModelRingedSite B S hS p hp).J (Type u),
          Sheaf.IsLocallySurjective (terminal.from H) →
            ∃ L ∈ T, Nonempty (L ⟶ H) ∧ Sheaf.IsLocallySurjective (terminal.from L)) ∧
        ∀ L ∈ T, Sheaf.IsQuasiCompact (L ⨯ L))
    [PreservesColimitsOfShape K
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι]
    [HasColimit D] [HasColimit (D ⋙ coyoneda.obj (Opposite.op G))] :
    IsIso (colimit.post D (coyoneda.obj (Opposite.op G))) :=
  have _ := (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringStructureSheafCore B S hS p hp .fppf)).preservesColimitsOfShape_coyoneda_fullSubcategory
      G K (preservesColimitsOfShape_coyoneda_fppf_of_isFinitePresentation_model
        B S hS p hp G.obj
        (isFinitePresentation_modulesEquivFppfModelModules B S hS p hp G.obj hG) K hX)
  inferInstance

end FppfSiteOfStack

end AlgebraicGeometry.FibredSite

end
