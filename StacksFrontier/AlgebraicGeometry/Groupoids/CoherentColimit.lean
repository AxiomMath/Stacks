module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FilteredColimit
public import StacksFrontier.AlgebraicGeometry.Cohomology.ColimitsHigherDirect.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidColimits
public import StacksFrontier.AlgebraicGeometry.Groupoids.Coinduction
public import StacksFrontier.AlgebraicGeometry.Groupoids.CoinductionAdjunction
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentIso
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward

/-!
# Coherent approximation of a quasi-coherent module on a groupoid scheme

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` and `R` Noetherian and with `s`
and `t` flat, quasi-compact and quasi-separated, and let `(ℱ, β)` be a quasi-coherent module on
it.  Then `(ℱ, β)` is a filtered colimit of quasi-coherent modules on the groupoid scheme whose
underlying modules on `U` are coherent.

The construction is the one of the source.  On the Noetherian scheme `U` the module `ℱ` is the
filtered colimit of its coherent submodules `ℋ`, and for each of them the submodule
`ℱ_ℋ ⊆ ℱ` of sections whose image under `β ∘ t^*` lies in `t^* ℋ` is cut out as the fibre
product of the canonical morphism `u : ℱ ⟶ s_* t^* ℱ` with `s_* t^* ℋ ⟶ s_* t^* ℱ`.  Flatness
of `t` makes `t^* ℋ ⟶ t^* ℱ ≅ s^* ℱ` a monomorphism, so `ℱ_ℋ` is coherent by Tag 07TT; the
canonical isomorphism `α` of Tag 07TR restricts `β` to a descent morphism on `ℱ_ℋ`; and `s_*`
commutes with filtered colimits because `s` is quasi-compact and quasi-separated, so `ℱ` is the
colimit of the `ℱ_ℋ`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.coinductionUnitHom` is the canonical morphism
  `u : ℱ ⟶ s_* t^* ℱ`, the unit of `s^* ⊣ s_*` followed by the direct image of `β⁻¹`.
* `AlgebraicGeometry.GroupoidScheme.descentSubmodule` equips a quasi-coherent submodule of the
  underlying module of a quasi-coherent module on a groupoid scheme with a descent morphism.
* `AlgebraicGeometry.GroupoidScheme.approxObj` is the coherent approximation `ℱ_ℋ` attached to a
  submodule `ℋ ⊆ ℱ`, as a quasi-coherent module on the groupoid scheme.

## Main results

* `AlgebraicGeometry.GroupoidScheme.pushforward_preservesFilteredColimits`: the direct image
  along a quasi-compact quasi-separated morphism of schemes preserves filtered colimits of
  modules.
* `AlgebraicGeometry.GroupoidScheme.isCoherent_approxObj`: the coherent approximation is
  coherent.
* `AlgebraicGeometry.GroupoidScheme.exists_filtered_diagram_isCoherent_of_coinductionUnitComm`
  and `AlgebraicGeometry.GroupoidScheme.exists_filtered_diagram_of_isCoherent`: **Tag 07TU**,
  the second being the first with its hypothesis on the canonical morphism discharged.

## Implementation notes

The construction uses of the coinduced module `(s_* t^* 𝒢, α)` only the morphism `α` and its
naturality, together with the compatibility `β ≫ s^* u = t^* u ≫ α` of the canonical morphism
`u : ℱ ⟶ s_* t^* ℱ` with the descent morphisms.  The main theorem is therefore proved first with
that compatibility as a hypothesis, and the hypothesis is then discharged from Tag 0GNF, which
identifies `u` with the unit of the coinduction adjunction.  In particular neither the cocycle
condition nor the normalization along the identity section for `α` enters the argument, because
the descent morphism of `ℱ_ℋ` is obtained from `β` by restriction along a monomorphism, and both
conditions for a restricted descent morphism follow from those for `β`.

The diagram is indexed by the coherent submodules of `ℱ`, which form a category one universe
above the schemes; it is only essentially small, so colimits over it and their exactness are
transported from its small model.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 07TB](https://stacks.math.columbia.edu/tag/07TB)
* [Stacks Project, Tag 0GNF](https://stacks.math.columbia.edu/tag/0GNF)
* [Stacks Project, Tag 07TR](https://stacks.math.columbia.edu/tag/07TR)
* [Stacks Project, Tag 07TT](https://stacks.math.columbia.edu/tag/07TT)
* [Stacks Project, Tag 07TU](https://stacks.math.columbia.edu/tag/07TU)
* [Stacks Project, Tag 0GN6](https://stacks.math.columbia.edu/tag/0GN6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open Stacks.Groupoids.GroupoidScheme

universe v v₂ w w₂ u

namespace AlgebraicGeometry.GroupoidScheme

/-! ### Transport of coherence along an isomorphism -/

/-- Coherence of a module on a locally Noetherian scheme is invariant under isomorphism. -/
theorem isCoherent_of_iso {X : Scheme.{u}} [IsLocallyNoetherian X] {F H : X.Modules}
    (e : F ≅ H) (hF : F.IsCoherent) : H.IsCoherent := by
  refine ((Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae X H).out 3 1).mp ?_
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e
    (((Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae X F).out 1 3).mp hF)

/-! ### Direct images and filtered colimits -/

/-- The comparison of the direct image of modules with the direct image of the underlying
sheaves of abelian groups. -/
noncomputable def pushforwardToSheafIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pushforward f ⋙ SheafOfModules.toSheaf Y.ringCatSheaf ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The forgetful functor from modules on a scheme to sheaves of abelian groups preserves
filtered colimits. -/
theorem toSheaf_preservesFilteredColimits (X : Scheme.{u}) :
    PreservesFilteredColimits (SheafOfModules.toSheaf.{u, u, u, u} X.ringCatSheaf) := by
  refine ⟨fun I _ _ => ?_⟩
  refine ⟨?_⟩
  intro D
  refine ⟨?_⟩
  intro c hc
  let L := PresheafOfModules.sheafification.{u, u, u, u} (𝟙 X.ringCatSheaf.obj)
  let adj : L ⊣ _ := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let Gf := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  have hL : PreservesColimitsOfShape I L :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hS : PreservesColimitsOfShape I
      (presheafToSheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
    (sheafificationAdjunction (Opens.grothendieckTopology X.carrier)
      AddCommGrpCat.{u}).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hLT : PreservesColimitsOfShape I
      (L ⋙ SheafOfModules.toSheaf.{u, u, u, u} X.ringCatSheaf) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 X.ringCatSheaf.obj)).symm
  have e : (D ⋙ Gf) ⋙ L ≅ D :=
    NatIso.ofComponents (fun j => (asIso adj.counit).app (D.obj j))
      (fun f => (asIso adj.counit).hom.naturality (D.map f))
  have : PreservesColimit (D ⋙ Gf) L := hL.preservesColimit
  have : PreservesColimit (D ⋙ Gf)
      (L ⋙ SheafOfModules.toSheaf.{u, u, u, u} X.ringCatSheaf) := hLT.preservesColimit
  have : PreservesColimit ((D ⋙ Gf) ⋙ L)
      (SheafOfModules.toSheaf.{u, u, u, u} X.ringCatSheaf) := by
    refine preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves L (colimit.isColimit (D ⋙ Gf))) ?_
    exact isColimitOfPreserves (L ⋙ SheafOfModules.toSheaf.{u, u, u, u} X.ringCatSheaf)
      (colimit.isColimit (D ⋙ Gf))
  exact (preservesColimit_of_iso_diagram
    (SheafOfModules.toSheaf.{u, u, u, u} X.ringCatSheaf) e).preserves hc

/-- The direct image of modules along a quasi-compact and quasi-separated morphism of schemes
preserves filtered colimits.  This is Tag 07TB in degree zero, read on modules. -/
@[sga "4 VI 8.5.11" "special case"]
theorem pushforward_preservesFilteredColimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    PreservesFilteredColimits (Scheme.Modules.pushforward f) := by
  refine ⟨fun I _ _ => ?_⟩
  have hsource : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u, u, u, u} X.ringCatSheaf) :=
    (toSheaf_preservesFilteredColimits X).preserves_filtered_colimits I
  have htarget : PreservesColimitsOfShape I (SheafOfModules.toSheaf.{u, u, u, u} Y.ringCatSheaf) :=
    (toSheaf_preservesFilteredColimits Y).preserves_filtered_colimits I
  have hP : PreservesColimitsOfShape I (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base) := by
    let : PreservesColimitsOfShape I
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).rightDerived 0) :=
      (Stacks.Cohomology.SchemeColimits.higherDirectImage_preservesFilteredColimits f
        0).preserves_filtered_colimits I
    exact preservesColimitsOfShape_of_natIso
      (Functor.rightDerivedZeroIsoSelf (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base))
  have hcomp : PreservesColimitsOfShape I
      (Scheme.Modules.pushforward f ⋙ SheafOfModules.toSheaf.{u, u, u, u} Y.ringCatSheaf) := by
    refine (preservesColimitsOfShape_iff_of_natIso (pushforwardToSheafIso f)).mpr ?_
    refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
    have hc' : IsColimit ((SheafOfModules.toSheaf.{u, u, u, u} X.ringCatSheaf).mapCocone c) :=
      (hsource.preservesColimit.preserves hc).some
    exact hP.preservesColimit.preserves hc'
  have : ReflectsColimitsOfShape I (SheafOfModules.toSheaf.{u, u, u, u} Y.ringCatSheaf) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
  exact this.reflectsColimit.reflects
      (isColimitOfPreserves
        (Scheme.Modules.pushforward f ⋙ SheafOfModules.toSheaf.{u, u, u, u} Y.ringCatSheaf) hc)

/-! ### Flatness of the projections of the scheme of composable arrows -/

variable {S : Scheme.{u}} {G : Stacks.Groupoids.GroupoidScheme S}

/-- The second projection of the scheme of composable arrows is flat, being a base change of
the source map. -/
theorem flat_snd_left [Flat G.source.left] : Flat (pullback.snd G.source G.target).left := by
  have h : Flat ((overPullbackLeftIso G.source G.target).hom ≫
    pullback.snd G.source.left G.target.left) := inferInstance
  rwa [overPullbackLeftIso_hom_snd] at h

/-- Inverse image of modules along the composite of the composition morphism with the source is
left exact: that composite is the composite of the second projection with the source. -/
theorem preservesFiniteLimits_pullback_comp_source [Flat G.source.left] :
    PreservesFiniteLimits (Scheme.Modules.pullback (G.comp.left ≫ G.source.left)) := by
  let : Flat (pullback.snd G.source G.target).left := flat_snd_left
  let : PreservesFiniteLimits
      (Scheme.Modules.pullback (pullback.snd G.source G.target).left) :=
    preservesFiniteLimits_modulesPullback_of_flat _
  let : PreservesFiniteLimits (Scheme.Modules.pullback G.source.left) :=
    preservesFiniteLimits_modulesPullback_of_flat _
  have hcomp : PreservesFiniteLimits (Scheme.Modules.pullback
      ((pullback.snd G.source G.target).left ≫ G.source.left)) :=
    preservesFiniteLimits_of_natIso (Scheme.Modules.pullbackComp
      (pullback.snd G.source G.target).left G.source.left)
  exact preservesFiniteLimits_of_natIso
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left G.source_comp).symm)

/-! ### Restriction of a descent morphism to a submodule -/

/-- Inverse image of modules along a flat morphism preserves monomorphisms. -/
private theorem mono_modulesPullback_map_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {N N' : Y.Modules} (j : N ⟶ N') [Mono j] : Mono ((Scheme.Modules.pullback f).map j) :=
  have := preservesFiniteLimits_modulesPullback_of_flat f
  preserves_mono_of_preservesLimit _ j

/-- A quasi-coherent submodule of the underlying module of a quasi-coherent module on a groupoid
scheme, equipped with a descent morphism compatible with the inclusion, is a quasi-coherent
module on the groupoid scheme: the cocycle condition and the normalization along the identity
section are inherited from those of the ambient module by cancelling the monomorphism. -/
noncomputable def descentSubmodule [Flat G.source.left] (M : QuasicoherentModule G)
    (K : G.objects.left.Modules) [K.IsQuasicoherent] (i : K ⟶ M.module) [Mono i]
    (a : (Scheme.Modules.pullback G.target.left).obj K ⟶
      (Scheme.Modules.pullback G.source.left).obj K)
    (ha : a ≫ (Scheme.Modules.pullback G.source.left).map i =
      (Scheme.Modules.pullback G.target.left).map i ≫ M.alpha) :
    QuasicoherentModule G where
  module := K
  isQuasicoherent := inferInstance
  alpha := a
  cocycle := by
    let := preservesFiniteLimits_pullback_comp_source (G := G)
    have : Mono ((Scheme.Modules.pullback (G.comp.left ≫ G.source.left)).map i) :=
      preserves_mono_of_preservesLimit _ i
    refine (cancel_mono ((Scheme.Modules.pullback (G.comp.left ≫ G.source.left)).map i)).1 ?_
    rw [successiveDescent_naturality G a M.alpha i ha,
      reindexHom_naturality G.comp.left a M.alpha i ha, M.cocycle]
  identity := by
    refine (cancel_mono i).1 ?_
    rw [identityDescent_naturality G a M.alpha i ha, M.identity, Category.comp_id,
      Category.id_comp]

/-- The underlying module of `descentSubmodule M K i a ha` is `K`. -/
@[simp]
theorem descentSubmodule_module [Flat G.source.left] (M : QuasicoherentModule G)
    (K : G.objects.left.Modules) [K.IsQuasicoherent] (i : K ⟶ M.module) [Mono i]
    (a : (Scheme.Modules.pullback G.target.left).obj K ⟶
      (Scheme.Modules.pullback G.source.left).obj K)
    (ha : a ≫ (Scheme.Modules.pullback G.source.left).map i =
      (Scheme.Modules.pullback G.target.left).map i ≫ M.alpha) :
    (descentSubmodule M K i a ha).module = K :=
  rfl

/-- The descent morphism of `descentSubmodule M K i a ha` is `a`. -/
@[simp]
theorem descentSubmodule_alpha [Flat G.source.left] (M : QuasicoherentModule G)
    (K : G.objects.left.Modules) [K.IsQuasicoherent] (i : K ⟶ M.module) [Mono i]
    (a : (Scheme.Modules.pullback G.target.left).obj K ⟶
      (Scheme.Modules.pullback G.source.left).obj K)
    (ha : a ≫ (Scheme.Modules.pullback G.source.left).map i =
      (Scheme.Modules.pullback G.target.left).map i ≫ M.alpha) :
    (descentSubmodule M K i a ha).alpha = a :=
  rfl

/-- A morphism between two submodules of the underlying module of `M` which commutes with the
inclusions into `M` commutes with the restricted descent morphisms. -/
theorem descentSubmodule_hom_comm (M : QuasicoherentModule G)
    {K K' : G.objects.left.Modules} (i : K ⟶ M.module) (i' : K' ⟶ M.module)
    [Mono ((Scheme.Modules.pullback G.source.left).map i')]
    {a : (Scheme.Modules.pullback G.target.left).obj K ⟶
      (Scheme.Modules.pullback G.source.left).obj K}
    {a' : (Scheme.Modules.pullback G.target.left).obj K' ⟶
      (Scheme.Modules.pullback G.source.left).obj K'}
    (ha : a ≫ (Scheme.Modules.pullback G.source.left).map i =
      (Scheme.Modules.pullback G.target.left).map i ≫ M.alpha)
    (ha' : a' ≫ (Scheme.Modules.pullback G.source.left).map i' =
      (Scheme.Modules.pullback G.target.left).map i' ≫ M.alpha)
    (k : K ⟶ K') (hk : k ≫ i' = i) :
    a ≫ (Scheme.Modules.pullback G.source.left).map k =
      (Scheme.Modules.pullback G.target.left).map k ≫ a' := by
  refine (cancel_mono ((Scheme.Modules.pullback G.source.left).map i')).1 ?_
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, hk, ha, ha', ← Category.assoc,
    ← Functor.map_comp, hk]

/-! ### The canonical morphism to the coinduced module -/

/-- The canonical morphism `ℱ ⟶ s_* t^* ℱ` attached to a quasi-coherent module `(ℱ, β)` on a
groupoid scheme: the unit of `s^* ⊣ s_*` followed by the direct image of the inverse of the
descent morphism. -/
noncomputable def coinductionUnitHom (M : QuasicoherentModule G) :
    M.module ⟶ (Scheme.Modules.pushforward G.source.left).obj
      ((Scheme.Modules.pullback G.target.left).obj M.module) :=
  (Scheme.Modules.pullbackPushforwardAdjunction G.source.left).unit.app M.module ≫
    (Scheme.Modules.pushforward G.source.left).map (inv M.alpha)

/-- The canonical morphism `coinductionUnitHom M` followed by the direct image along the source of
the descent morphism of `M` is the unit of `s^* ⊣ s_*` at the underlying module of `M`. -/
theorem coinductionUnitHom_comp_pushforward_alpha (M : QuasicoherentModule G) :
    coinductionUnitHom M ≫ (Scheme.Modules.pushforward G.source.left).map M.alpha =
      (Scheme.Modules.pullbackPushforwardAdjunction G.source.left).unit.app M.module := by
  rw [coinductionUnitHom, Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id,
    CategoryTheory.Functor.map_id]
  simp

/-! ### The coherent approximation attached to a submodule -/

/-- The source map of a groupoid scheme is surjective: the identity section is a section of
it. -/
theorem surjective_source_left : Surjective G.source.left := by
  refine ⟨fun x => ⟨G.identity.left.base x, ?_⟩⟩
  simpa using congrArg (fun f : G.objects.left ⟶ G.objects.left => f.base x)
    (congrArg Over.Hom.left G.source_identity)

/-- The direct image along the source of the inverse image along the target of a monomorphism
is a monomorphism. -/
theorem mono_pushforwardSource_pullbackTarget [Flat G.target.left]
    {N N' : G.objects.left.Modules} (j : N ⟶ N') [Mono j] :
    Mono ((Scheme.Modules.pushforward G.source.left).map
      ((Scheme.Modules.pullback G.target.left).map j)) := by
  have := mono_modulesPullback_map_of_flat G.target.left j
  infer_instance

/-- The underlying module of the coherent approximation of `(ℱ, β)` attached to a submodule
`j : 𝒩 ⟶ ℱ`: the fibre product of the canonical morphism `u : ℱ ⟶ s_* t^* ℱ` with the direct
image along the source of the inverse image along the target of `j`. -/
noncomputable def approxModule (M : QuasicoherentModule G) {N : G.objects.left.Modules}
    (j : N ⟶ M.module) : G.objects.left.Modules :=
  pullback (coinductionUnitHom M)
    ((Scheme.Modules.pushforward G.source.left).map
      ((Scheme.Modules.pullback G.target.left).map j))

/-- The inclusion of the coherent approximation into the ambient module. -/
noncomputable def approxι (M : QuasicoherentModule G) {N : G.objects.left.Modules}
    (j : N ⟶ M.module) : approxModule M j ⟶ M.module :=
  pullback.fst _ _

/-- The second projection of the coherent approximation. -/
noncomputable def approxπ (M : QuasicoherentModule G) {N : G.objects.left.Modules}
    (j : N ⟶ M.module) :
    approxModule M j ⟶ (Scheme.Modules.pushforward G.source.left).obj
      ((Scheme.Modules.pullback G.target.left).obj N) :=
  pullback.snd _ _

/-- The defining square of the coherent approximation commutes: `approxι M j` followed by the
canonical morphism `coinductionUnitHom M` equals `approxπ M j` followed by the direct image along
the source of the inverse image along the target of `j`. -/
theorem approxι_comp_coinductionUnitHom (M : QuasicoherentModule G)
    {N : G.objects.left.Modules} (j : N ⟶ M.module) :
    approxι M j ≫ coinductionUnitHom M =
      approxπ M j ≫ (Scheme.Modules.pushforward G.source.left).map
        ((Scheme.Modules.pullback G.target.left).map j) :=
  pullback.condition

/-- The defining square of the coherent approximation, with sides `approxι M j`, `approxπ M j`,
`coinductionUnitHom M` and the direct image along the source of the inverse image along the
target of `j`, is cartesian. -/
theorem isPullback_approx (M : QuasicoherentModule G) {N : G.objects.left.Modules}
    (j : N ⟶ M.module) :
    IsPullback (approxι M j) (approxπ M j) (coinductionUnitHom M)
      ((Scheme.Modules.pushforward G.source.left).map
        ((Scheme.Modules.pullback G.target.left).map j)) :=
  IsPullback.of_hasPullback _ _

/-- If the target map is flat and `j` is a monomorphism, then the inclusion `approxι M j` of the
coherent approximation into the ambient module is a monomorphism. -/
theorem mono_approxι [Flat G.target.left] (M : QuasicoherentModule G)
    {N : G.objects.left.Modules} (j : N ⟶ M.module) [Mono j] : Mono (approxι M j) := by
  have := mono_pushforwardSource_pullbackTarget (G := G) j
  exact inferInstanceAs (Mono (pullback.fst (coinductionUnitHom M)
    ((Scheme.Modules.pushforward G.source.left).map
      ((Scheme.Modules.pullback G.target.left).map j))))

/-- If the source map is quasi-compact and quasi-separated and `N` is quasi-coherent, then the
underlying module `approxModule M j` of the coherent approximation is quasi-coherent. -/
theorem isQuasicoherent_approxModule [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    (M : QuasicoherentModule G) {N : G.objects.left.Modules} (hN : N.IsQuasicoherent)
    (j : N ⟶ M.module) : (approxModule M j).IsQuasicoherent := by
  have := hN
  have := isQuasicoherent_pushforwardSource_pullbackTarget G N
  have := isQuasicoherent_pushforwardSource_pullbackTarget G M.module
  exact inferInstanceAs (pullback (coinductionUnitHom M)
    ((Scheme.Modules.pushforward G.source.left).map
      ((Scheme.Modules.pullback G.target.left).map j))).IsQuasicoherent

/-- After inverse image along the source the defining square of the coherent approximation is
still cartesian, because the source map is flat. -/
theorem isPullback_pullbackSource_approx [Flat G.source.left] (M : QuasicoherentModule G)
    {N : G.objects.left.Modules} (j : N ⟶ M.module) :
    IsPullback ((Scheme.Modules.pullback G.source.left).map (approxι M j))
      ((Scheme.Modules.pullback G.source.left).map (approxπ M j))
      ((Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M))
      ((Scheme.Modules.pullback G.source.left).map
        ((Scheme.Modules.pushforward G.source.left).map
          ((Scheme.Modules.pullback G.target.left).map j))) := by
  have : PreservesFiniteLimits (Scheme.Modules.pullback G.source.left) :=
    preservesFiniteLimits_modulesPullback_of_flat _
  exact (Scheme.Modules.pullback G.source.left).map_isPullback (isPullback_approx M j)

/-- The descent morphism of the coherent approximation: the inverse image along the target of
its inclusion followed by `β`, and the inverse image along the target of its second projection
followed by the canonical isomorphism `α` of Tag 07TR, agree over `s^* s_* t^* ℱ`, so they
factor through the inverse image along the source of the approximation. -/
noncomputable def approxDescent [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] (M : QuasicoherentModule G)
    {N : G.objects.left.Modules} (hN : N.IsQuasicoherent) (j : N ⟶ M.module)
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    (Scheme.Modules.pullback G.target.left).obj (approxModule M j) ⟶
      (Scheme.Modules.pullback G.source.left).obj (approxModule M j) :=
  have : N.IsQuasicoherent := hN
  (isPullback_pullbackSource_approx M j).lift
    ((Scheme.Modules.pullback G.target.left).map (approxι M j) ≫ M.alpha)
    ((Scheme.Modules.pullback G.target.left).map (approxπ M j) ≫ (coinductionAlpha G N).hom)
    (by
      have hnat := coinductionAlpha_naturality G (𝒢 := N) (𝒢' := M.module) j
      calc ((Scheme.Modules.pullback G.target.left).map (approxι M j) ≫ M.alpha) ≫
              (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M)
          = (Scheme.Modules.pullback G.target.left).map (approxι M j) ≫
              (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
                (coinductionAlpha G M.module).hom := by rw [Category.assoc, hu]
        _ = (Scheme.Modules.pullback G.target.left).map (approxπ M j) ≫
              (Scheme.Modules.pullback G.target.left).map
                  ((Scheme.Modules.pushforward G.source.left).map
                    ((Scheme.Modules.pullback G.target.left).map j)) ≫
                (coinductionAlpha G M.module).hom := by
              rw [← Category.assoc, ← Functor.map_comp, approxι_comp_coinductionUnitHom,
                Functor.map_comp, Category.assoc]
        _ = ((Scheme.Modules.pullback G.target.left).map (approxπ M j) ≫
              (coinductionAlpha G N).hom) ≫
              (Scheme.Modules.pullback G.source.left).map
                ((Scheme.Modules.pushforward G.source.left).map
                  ((Scheme.Modules.pullback G.target.left).map j)) := by
              rw [Category.assoc, hnat])

/-- The descent morphism `approxDescent M hN j hu` is compatible with the inclusion `approxι M j`
and the descent morphism of `M`. -/
theorem approxDescent_comp_approxι [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] (M : QuasicoherentModule G)
    {N : G.objects.left.Modules} (hN : N.IsQuasicoherent) (j : N ⟶ M.module)
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    approxDescent M hN j hu ≫ (Scheme.Modules.pullback G.source.left).map (approxι M j) =
      (Scheme.Modules.pullback G.target.left).map (approxι M j) ≫ M.alpha :=
  (isPullback_pullbackSource_approx M j).lift_fst _ _ _

/-- **The coherent approximation of `(ℱ, β)` attached to a submodule `𝒩 ⊆ ℱ`**, as a
quasi-coherent module on the groupoid scheme. -/
noncomputable def approxObj [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] (M : QuasicoherentModule G)
    {N : G.objects.left.Modules} (hN : N.IsQuasicoherent) (j : N ⟶ M.module) [Mono j]
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    QuasicoherentModule G :=
  have : Mono (approxι M j) := mono_approxι M j
  have : (approxModule M j).IsQuasicoherent := isQuasicoherent_approxModule M hN j
  descentSubmodule M (approxModule M j) (approxι M j) (approxDescent M hN j hu)
    (approxDescent_comp_approxι M hN j hu)

/-- The underlying module of `approxObj M hN j hu` is `approxModule M j`. -/
@[simp]
theorem approxObj_module [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] (M : QuasicoherentModule G)
    {N : G.objects.left.Modules} (hN : N.IsQuasicoherent) (j : N ⟶ M.module) [Mono j]
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    (approxObj M hN j hu).module = approxModule M j :=
  rfl

/-- The descent morphism of `approxObj M hN j hu` is `approxDescent M hN j hu`. -/
@[simp]
theorem approxObj_alpha [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] (M : QuasicoherentModule G)
    {N : G.objects.left.Modules} (hN : N.IsQuasicoherent) (j : N ⟶ M.module) [Mono j]
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    (approxObj M hN j hu).alpha = approxDescent M hN j hu :=
  rfl

/-! ### Coherence of the approximation -/

/-- **Stacks Project, Tag 07TT** applied to the source map of the groupoid scheme: the coherent
approximation attached to a coherent submodule of `ℱ` is coherent. -/
theorem isCoherent_approxModule [IsNoetherian G.objects.left] [IsNoetherian G.arrows.left]
    [Flat G.source.left] [Flat G.target.left] [QuasiCompact G.source.left]
    [QuasiSeparated G.source.left] (M : QuasicoherentModule G)
    {N : G.objects.left.Modules} (hN : N.IsQuasicoherent) (hNcoh : N.IsCoherent)
    (j : N ⟶ M.module) [Mono j] : (approxModule M j).IsCoherent := by
  have := hN
  have hNqcft : N.IsQuasicoherent ∧ N.IsFiniteType :=
    ((Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae G.objects.left N).out 1 2).mp hNcoh
  have hNft : N.IsFiniteType := hNqcft.2
  have hTqc : ((Scheme.Modules.pullback G.target.left).obj N).IsQuasicoherent :=
    isQuasicoherent_pullbackTarget G N
  have hTft : ((Scheme.Modules.pullback G.target.left).obj N).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType G.target.left.toLRSHom.toShHom N
  have hTcoh : ((Scheme.Modules.pullback G.target.left).obj N).IsCoherent := by
    refine ((Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae G.arrows.left
      ((Scheme.Modules.pullback G.target.left).obj N)).out 2 1).mp ?_
    exact ⟨hTqc, hTft⟩
  have hmonoj := mono_modulesPullback_map_of_flat G.target.left j
  have : Mono M.alpha := @IsIso.mono_of_iso _ _ _ _ _ (QuasicoherentModule.alpha_isIso M)
  have hmono : Mono ((Scheme.Modules.pullback G.target.left).map j ≫ M.alpha) :=
    mono_comp _ _
  have : Surjective G.source.left := surjective_source_left
  have h07TT := isCoherent_pullback_pushforward G.source.left M.module
    ((Scheme.Modules.pullback G.target.left).obj N)
    ((Scheme.Modules.pullback G.target.left).map j ≫ M.alpha)
  have heq₁ : coinductionUnitHom M ≫ (Scheme.Modules.pushforward G.source.left).map M.alpha =
      𝟙 M.module ≫
        (Scheme.Modules.pullbackPushforwardAdjunction G.source.left).unit.app M.module := by
    rw [Category.id_comp]
    exact coinductionUnitHom_comp_pushforward_alpha M
  have heq₂ : (Scheme.Modules.pushforward G.source.left).map
        ((Scheme.Modules.pullback G.target.left).map j) ≫
        (Scheme.Modules.pushforward G.source.left).map M.alpha =
      𝟙 _ ≫ (Scheme.Modules.pushforward G.source.left).map
        ((Scheme.Modules.pullback G.target.left).map j ≫ M.alpha) := by
    rw [Category.id_comp, Functor.map_comp]
  have : IsIso ((Scheme.Modules.pushforward G.source.left).map M.alpha) := inferInstance
  have hiso : IsIso (pullback.map (coinductionUnitHom M)
      ((Scheme.Modules.pushforward G.source.left).map
        ((Scheme.Modules.pullback G.target.left).map j))
      ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).unit.app M.module)
      ((Scheme.Modules.pushforward G.source.left).map
        ((Scheme.Modules.pullback G.target.left).map j ≫ M.alpha))
      (𝟙 _) (𝟙 _) ((Scheme.Modules.pushforward G.source.left).map M.alpha) heq₁ heq₂) :=
    inferInstance
  exact isCoherent_of_iso (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
    ((Scheme.Modules.pushforward G.source.left).map M.alpha) heq₁ heq₂)).symm h07TT

/-! ### Colimits of quasi-coherent modules on a groupoid scheme -/

/-- Quasi-coherence of a coherent module on a locally Noetherian scheme. -/
theorem isQuasicoherent_of_isCoherent {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    (hF : F.IsCoherent) : F.IsQuasicoherent := by
  have h : F.IsQuasicoherent ∧ F.IsFiniteType :=
    ((Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae X F).out 1 2).mp hF
  exact h.1

/-- A cocone of quasi-coherent modules on a groupoid scheme is colimiting as soon as it is
colimiting on the underlying modules and stays colimiting after inverse image along the
target. -/
noncomputable def isColimitOfUnderlying {I : Type (u + 1)} [Category.{v} I]
    (F : I ⥤ QuasicoherentModule G) (c : Cocone F)
    (hc : IsColimit ((QuasicoherentModule.forget G).mapCocone c))
    (hct : IsColimit ((Scheme.Modules.pullback G.target.left).mapCocone
      ((QuasicoherentModule.forget G).mapCocone c))) : IsColimit c := by
  have hfac (s : Cocone F) (i : I) :
      (c.ι.app i).hom ≫ hc.desc ((QuasicoherentModule.forget G).mapCocone s) =
        (s.ι.app i).hom :=
    hc.fac ((QuasicoherentModule.forget G).mapCocone s) i
  have hcomm (i : I) : (F.obj i).alpha ≫
      (Scheme.Modules.pullback G.source.left).map (c.ι.app i).hom =
      (Scheme.Modules.pullback G.target.left).map (c.ι.app i).hom ≫ c.pt.alpha :=
    (c.ι.app i).comm
  have hcommS (s : Cocone F) (i : I) : (F.obj i).alpha ≫
      (Scheme.Modules.pullback G.source.left).map (s.ι.app i).hom =
      (Scheme.Modules.pullback G.target.left).map (s.ι.app i).hom ≫ s.pt.alpha :=
    (s.ι.app i).comm
  refine
    { desc := fun s =>
        { hom := hc.desc ((QuasicoherentModule.forget G).mapCocone s)
          comm := ?_ }
      fac := ?_
      uniq := ?_ }
  · refine hct.hom_ext fun i => ?_
    calc (Scheme.Modules.pullback G.target.left).map (c.ι.app i).hom ≫ c.pt.alpha ≫
            (Scheme.Modules.pullback G.source.left).map
              (hc.desc ((QuasicoherentModule.forget G).mapCocone s))
        = (F.obj i).alpha ≫ (Scheme.Modules.pullback G.source.left).map
            ((c.ι.app i).hom ≫ hc.desc ((QuasicoherentModule.forget G).mapCocone s)) := by
          rw [Functor.map_comp, ← Category.assoc, ← hcomm i, Category.assoc]
      _ = (F.obj i).alpha ≫ (Scheme.Modules.pullback G.source.left).map (s.ι.app i).hom := by
          rw [hfac]
      _ = (Scheme.Modules.pullback G.target.left).map (s.ι.app i).hom ≫ s.pt.alpha :=
          hcommS s i
      _ = (Scheme.Modules.pullback G.target.left).map (c.ι.app i).hom ≫
            (Scheme.Modules.pullback G.target.left).map
              (hc.desc ((QuasicoherentModule.forget G).mapCocone s)) ≫ s.pt.alpha := by
          rw [← hfac s i, Functor.map_comp, Category.assoc]
  · intro s i
    apply QuasicoherentModule.Hom.ext
    exact hfac s i
  · intro s m hm
    apply QuasicoherentModule.Hom.ext
    refine hc.uniq ((QuasicoherentModule.forget G).mapCocone s) m.hom fun i => ?_
    exact congrArg QuasicoherentModule.Hom.hom (hm i)

/-- A diagram of fibre products over a fixed morphism, indexed by a connected category in which
colimits are exact, has colimit the fibre product of the colimits.  Here the right-hand column
is constant, so the colimit of the diagram is the source of the fixed morphism. -/
noncomputable def isColimitOfPullback {C : Type w} [Category.{v} C] {J : Type w₂}
    [Category.{v₂} J] [IsConnected J] [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    {D E : J ⥤ C} {M N : C} (p : D ⟶ (Functor.const J).obj M) (q : D ⟶ E) (f : M ⟶ N)
    (b : E ⟶ (Functor.const J).obj N) (hb : IsColimit (Cocone.mk N b))
    (h : ∀ j, IsPullback (p.app j) (q.app j) f (b.app j)) :
    IsColimit (Cocone.mk M p) := by
  have hsq := IsPullback.of_forall_isPullback_app (f₃ := (Functor.const J).map f) h
  have hcol := (colim (J := J) (C := C)).map_isPullback hsq
  let eM : colimit ((Functor.const J).obj M) ≅ M :=
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J M)
  let eN : colimit ((Functor.const J).obj N) ≅ N :=
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone J N)
  let eE : colimit E ≅ N := (colimit.isColimit E).coconePointUniqueUpToIso hb
  have hb' : colim.map b ≫ eN.hom = eE.hom := by
    refine colimit.hom_ext fun j => ?_
    have h1 : colimit.ι E j ≫ eE.hom = (Cocone.mk N b).ι.app j :=
      (colimit.isColimit E).comp_coconePointUniqueUpToIso_hom hb j
    have h2 : colimit.ι ((Functor.const J).obj N) j ≫ eN.hom = (constCocone J N).ι.app j :=
      (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitConstCocone J N) j
    rw [← Category.assoc, colimit.ι_map, Category.assoc, h2, h1]
    simp
  haveI : IsIso (colim.map b ≫ eN.hom) := by
    rw [hb']
    infer_instance
  haveI : IsIso (colim.map b) := IsIso.of_isIso_comp_right _ eN.hom
  haveI : IsIso (colim.map p) := hcol.isIso_fst_of_isIso
  have hp : colimit.desc D (Cocone.mk M p) = colim.map p ≫ eM.hom := by
    refine colimit.hom_ext fun j => ?_
    have h2 : colimit.ι ((Functor.const J).obj M) j ≫ eM.hom = (constCocone J M).ι.app j :=
      (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitConstCocone J M) j
    rw [colimit.ι_desc, ← Category.assoc, colimit.ι_map, Category.assoc, h2]
    simp
  haveI : IsIso (colimit.desc D (Cocone.mk M p)) := by
    rw [hp]
    infer_instance
  haveI : IsIso ((colimit.isColimit D).desc (Cocone.mk M p)) := by
    simpa only [colimit.isColimit_desc] using
      (inferInstance : IsIso (colimit.desc D (Cocone.mk M p)))
  exact (colimit.isColimit D).ofPointIso

/-! ### The diagram of coherent approximations -/

/-- The morphism of coherent approximations induced by a morphism `k : 𝒩 ⟶ 𝒩'` of submodules of
`ℱ` over `ℱ`. -/
private noncomputable def approxMap (M : QuasicoherentModule G) {N N' : G.objects.left.Modules}
    {j : N ⟶ M.module} {j' : N' ⟶ M.module} (k : N ⟶ N') (hk : k ≫ j' = j) :
    approxModule M j ⟶ approxModule M j' :=
  pullback.lift (approxι M j)
    (approxπ M j ≫ (Scheme.Modules.pushforward G.source.left).map
      ((Scheme.Modules.pullback G.target.left).map k)) (by
    rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hk]
    exact approxι_comp_coinductionUnitHom M j)

/-- The morphism `approxMap M k hk` commutes with the inclusions into `ℱ`. -/
@[reassoc (attr := simp)]
private theorem approxMap_approxι (M : QuasicoherentModule G) {N N' : G.objects.left.Modules}
    {j : N ⟶ M.module} {j' : N' ⟶ M.module} (k : N ⟶ N') (hk : k ≫ j' = j) :
    approxMap M k hk ≫ approxι M j' = approxι M j :=
  pullback.lift_fst _ _ _

/-- The morphism `approxMap M k hk` commutes with the second projections. -/
@[reassoc (attr := simp)]
private theorem approxMap_approxπ (M : QuasicoherentModule G) {N N' : G.objects.left.Modules}
    {j : N ⟶ M.module} {j' : N' ⟶ M.module} (k : N ⟶ N') (hk : k ≫ j' = j) :
    approxMap M k hk ≫ approxπ M j' =
      approxπ M j ≫ (Scheme.Modules.pushforward G.source.left).map
        ((Scheme.Modules.pullback G.target.left).map k) :=
  pullback.lift_snd _ _ _

/-- Two morphisms into a coherent approximation agree as soon as they agree after `approxι` and
after `approxπ`. -/
private theorem approxModule_hom_ext (M : QuasicoherentModule G) {N : G.objects.left.Modules}
    {j : N ⟶ M.module} {X : G.objects.left.Modules} {f g : X ⟶ approxModule M j}
    (h₁ : f ≫ approxι M j = g ≫ approxι M j) (h₂ : f ≫ approxπ M j = g ≫ approxπ M j) :
    f = g :=
  pullback.hom_ext h₁ h₂

/-- The morphism of coherent approximations induced by a morphism of submodules of `ℱ` over
`ℱ`, as a morphism of quasi-coherent modules on the groupoid scheme. -/
private noncomputable def approxObjMap [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] (M : QuasicoherentModule G)
    {N N' : G.objects.left.Modules} (hN : N.IsQuasicoherent) (hN' : N'.IsQuasicoherent)
    {j : N ⟶ M.module} {j' : N' ⟶ M.module} [Mono j] [Mono j'] (k : N ⟶ N') (hk : k ≫ j' = j)
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    approxObj M hN j hu ⟶ approxObj M hN' j' hu where
  hom := approxMap M k hk
  comm := by
    have := mono_approxι M j'
    have := mono_modulesPullback_map_of_flat G.source.left (approxι M j')
    exact descentSubmodule_hom_comm M (approxι M j) (approxι M j')
      (approxDescent_comp_approxι M hN j hu) (approxDescent_comp_approxι M hN' j' hu)
      (approxMap M k hk) (approxMap_approxι M k hk)

/-- The diagram of the coherent approximations of `(ℱ, β)`, indexed by the coherent submodules
of `ℱ`. -/
private noncomputable def approxDiagram [IsLocallyNoetherian G.objects.left] [Flat G.source.left]
    [Flat G.target.left] [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    (M : QuasicoherentModule G)
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    CoherentSubobject M.module ⥤ QuasicoherentModule G where
  obj H := approxObj M (isQuasicoherent_of_isCoherent _ H.property) H.obj.arrow hu
  map {H H'} f := approxObjMap M (isQuasicoherent_of_isCoherent _ H.property)
    (isQuasicoherent_of_isCoherent _ H'.property) (Subobject.underlying.map f.hom)
    (Subobject.underlying_arrow f.hom) hu
  map_id H := by
    apply QuasicoherentModule.Hom.ext
    change _ = 𝟙 (approxModule M H.obj.arrow)
    exact approxModule_hom_ext M (by simp [approxObjMap]) (by simp [approxObjMap])
  map_comp f g := by
    apply QuasicoherentModule.Hom.ext
    change _ = _ ≫ _
    exact approxModule_hom_ext M (by simp [approxObjMap]) (by simp [approxObjMap])

/-- The cocone of the coherent approximations of `(ℱ, β)`, whose legs are their inclusions
into `ℱ`. -/
private noncomputable def approxDiagramι [IsLocallyNoetherian G.objects.left] [Flat G.source.left]
    [Flat G.target.left] [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    (M : QuasicoherentModule G)
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    approxDiagram M hu ⟶ (Functor.const _).obj M where
  app H :=
    { hom := approxι M H.obj.arrow
      comm := approxDescent_comp_approxι M (isQuasicoherent_of_isCoherent _ H.property)
        H.obj.arrow hu }
  naturality _ _ f := QuasicoherentModule.Hom.ext <|
    (approxMap_approxι M (Subobject.underlying.map f.hom) (Subobject.underlying_arrow f.hom)).trans
      (Category.comp_id _).symm

/-- On a Noetherian object scheme, a quasi-coherent module `(ℱ, β)` on the groupoid scheme is
the colimit of its coherent approximations. -/
private noncomputable def isColimitApproxDiagram [IsNoetherian G.objects.left] [Flat G.source.left]
    [Flat G.target.left] [QuasiCompact G.source.left] [QuasiSeparated G.source.left]
    (M : QuasicoherentModule G)
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    IsColimit (Cocone.mk M (approxDiagramι M hu)) := by
  let TP : G.objects.left.Modules ⥤ G.objects.left.Modules :=
    Scheme.Modules.pullback G.target.left ⋙ Scheme.Modules.pushforward G.source.left
  let U := QuasicoherentModule.forget G
  let ψ : approxDiagram M hu ⋙ U ⟶ coherentSubobjectFunctor M.module ⋙ TP :=
    { app := fun H => approxπ M H.obj.arrow
      naturality := fun {_ _} f =>
        approxMap_approxπ M (Subobject.underlying.map f.hom) (Subobject.underlying_arrow f.hom) }
  have : IsConnected (CoherentSubobject M.module) := IsFiltered.isConnected _
  let eI := equivSmallModel.{u} (CoherentSubobject M.module)
  have : IsFiltered (SmallModel.{u} (CoherentSubobject M.module)) := IsFiltered.of_equivalence eI
  have : HasColimitsOfShape (CoherentSubobject M.module) G.objects.left.Modules :=
    hasColimitsOfShape_of_equivalence eI.symm
  have : HasExactColimitsOfShape (CoherentSubobject M.module) G.objects.left.Modules :=
    HasExactColimitsOfShape.of_domain_equivalence _ eI.symm
  have : PreservesFilteredColimits (Scheme.Modules.pushforward G.source.left) :=
    pushforward_preservesFilteredColimits _
  have : PreservesColimitsOfShape (CoherentSubobject M.module)
      (Scheme.Modules.pushforward G.source.left) :=
    preservesColimitsOfShape_of_equiv eI.symm _
  have : PreservesColimitsOfShape (CoherentSubobject M.module)
      (Scheme.Modules.pullback G.target.left) :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      G.target.left).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape (CoherentSubobject M.module) TP := inferInstance
  have hcD : IsColimit (U.mapCocone (Cocone.mk M (approxDiagramι M hu))) :=
    isColimitOfPullback (U.mapCocone (Cocone.mk M (approxDiagramι M hu))).ι ψ
      (coinductionUnitHom M) (TP.mapCocone (coherentSubobjectCocone M.module)).ι
      (isColimitOfPreserves TP (isColimit_coherentSubobjectCocone M.module))
      fun H => isPullback_approx M H.obj.arrow
  exact isColimitOfUnderlying _ _ hcD
    (isColimitOfPreserves (Scheme.Modules.pullback G.target.left) hcD)

/-! ### Tag 07TU -/

/-- **Stacks Project, Tag 07TU**, with the compatibility of the canonical morphism
`u : ℱ ⟶ s_* t^* ℱ` with the descent morphisms carried as a hypothesis.

Let `(U, R, s, t, c)` be a groupoid scheme with `U` and `R` Noetherian and `s`, `t` flat,
quasi-compact and quasi-separated.  Then every quasi-coherent module `(ℱ, β)` on it is the
colimit of a filtered diagram of quasi-coherent modules on it whose underlying modules on `U`
are coherent.

The hypothesis `hu` is the equation `β ≫ s^* u = t^* u ≫ α` for the canonical morphism
`u : ℱ ⟶ s_* t^* ℱ` of `coinductionUnitHom` and the canonical isomorphism `α` of Tag 07TR; it is
discharged in `exists_filtered_diagram_of_isCoherent` below. -/
theorem exists_filtered_diagram_isCoherent_of_coinductionUnitComm
    [IsNoetherian G.objects.left] [IsNoetherian G.arrows.left]
    [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiCompact G.target.left]
    [QuasiSeparated G.source.left] [QuasiSeparated G.target.left]
    (M : QuasicoherentModule G)
    (hu : M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom) :
    ∃ (I : Type (u + 1)) (inst : SmallCategory I),
      let _ := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ QuasicoherentModule G)
        (φ : D ⟶ (Functor.const I).obj M),
        (∀ i, (D.obj i).module.IsCoherent) ∧
          Nonempty (IsColimit (Cocone.mk M φ)) := by
  refine ⟨CoherentSubobject M.module, inferInstance, inferInstance, approxDiagram M hu,
    approxDiagramι M hu, fun H => ?_, ⟨isColimitApproxDiagram M hu⟩⟩
  exact isCoherent_approxModule M (isQuasicoherent_of_isCoherent _ H.property) H.property
    H.obj.arrow

/-- **Stacks Project, Tag 0GNF** read as a compatibility.  The canonical morphism
`u : ℱ ⟶ s_* t^* ℱ` intertwines the descent morphism `β` of `(ℱ, β)` with the canonical
isomorphism `α` of `s_* t^* ℱ`: it is the unit of the coinduction adjunction, hence a morphism
of quasi-coherent modules on the groupoid scheme. -/
theorem coinductionUnitHom_comm [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiSeparated G.source.left] (M : QuasicoherentModule G) :
    M.alpha ≫ (Scheme.Modules.pullback G.source.left).map (coinductionUnitHom M) =
      (Scheme.Modules.pullback G.target.left).map (coinductionUnitHom M) ≫
        (coinductionAlpha G M.module).hom := by
  have h := ((coinductionAdjunction G).unit.app M).comm
  rwa [coinductionAdjunction_unit_app] at h

/-- **Stacks Project, Tag 07TU.**  Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U`
and `R` Noetherian and with `s` and `t` flat, quasi-compact and quasi-separated.  Then every
quasi-coherent module `(ℱ, β)` on the groupoid scheme is the colimit of a filtered diagram of
quasi-coherent modules on the groupoid scheme whose underlying modules on `U` are coherent. -/
@[stacks 07TU "every quasi-coherent module on the groupoid scheme is the colimit of a filtered \
diagram of quasi-coherent modules on the groupoid scheme with coherent underlying modules"]
theorem exists_filtered_diagram_of_isCoherent
    [IsNoetherian G.objects.left] [IsNoetherian G.arrows.left]
    [Flat G.source.left] [Flat G.target.left]
    [QuasiCompact G.source.left] [QuasiCompact G.target.left]
    [QuasiSeparated G.source.left] [QuasiSeparated G.target.left]
    (M : QuasicoherentModule G) :
    ∃ (I : Type (u + 1)) (inst : SmallCategory I),
      let _ := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ QuasicoherentModule G)
        (φ : D ⟶ (Functor.const I).obj M),
        (∀ i, (D.obj i).module.IsCoherent) ∧
          Nonempty (IsColimit (Cocone.mk M φ)) :=
  exists_filtered_diagram_isCoherent_of_coinductionUnitComm M (coinductionUnitHom_comm M)

end AlgebraicGeometry.GroupoidScheme

end
