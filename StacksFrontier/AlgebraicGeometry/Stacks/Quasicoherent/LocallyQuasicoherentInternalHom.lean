module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtalePrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FinitePresentationKernel
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization

/-!
# Internal Hom of locally quasi-coherent modules (Stacks 06WM, clause (5))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. Clause (5) of Stacks 06WM says
that for `F`, `G` in `LQCoh(𝒪_𝒳)` (Stacks 06WJ) with `F` of finite presentation on `𝒳_étale`,
the sheaf `𝓗om_{𝒪_𝒳}(F, G)` of `Mod(𝒳_étale, 𝒪_𝒳)` is again locally quasi-coherent.

The internal Hom is the one of Stacks 03EM on the associated étale site: its sections over `x`
are the morphisms `F|_{𝒳/x} ⟶ G|_{𝒳/x}`. These form a set of the universe of the sections of
`F` and `G`, since by Stacks 06W0 the slice `𝒳/x` is equivalent to a slice of the big site of
schemes and is therefore essentially small, so the internal Hom is a sheaf of modules in that
universe.

The proof is local, as in the source. Restricting a sheaf on `𝒳/x` to the small étale site of the
scheme below `x` factors through the restriction to the slice `𝒳/x`, on which the internal Hom
of `F` and `G` is the internal Hom of their restrictions (Stacks 0E8H). Over an object `y` over
which `F` has a finite presentation `𝒪^k ⟶ 𝒪^n ⟶ F|_{𝒳/y} ⟶ 0`, internal Hom into `G` turns it
into an exact sequence `0 ⟶ 𝓗om(F, G)|_{𝒳/y} ⟶ G^n ⟶ G^k`, because internal Hom carries
colimits in its first variable to limits and `𝓗om(𝒪, G) = G`. Restricting to the small étale
site of the scheme below `y` exhibits the restriction of `𝓗om(F, G)` as the kernel of a map
between finite products of copies of the restriction of `G`, which is quasi-coherent by
Descent, Lemma 0GNB. Finally every covering of an object of `𝒳_étale` on which `F` is finitely
presented is refined by arrows lying over a jointly surjective family of étale morphisms, and
quasi-coherence of the restriction is local for such families.

## Main definitions

* `AlgebraicGeometry.Stack.etaleInternalHom`: the internal Hom `𝓗om_{𝒪_𝒳}(F, G)` of Stacks 03EM
  in `Mod(𝒳_étale, 𝒪_𝒳)`, at the module universe of `F` and `G`.
* `AlgebraicGeometry.Stack.etaleInternalHomIso`: its universe lift is the internal Hom presheaf
  of Stacks 03EM.
* `AlgebraicGeometry.Stack.sliceRestrictToSmallEtale`: the restriction of Stacks 06WJ, read on
  the slice `𝒳/y`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_etaleInternalHom`: **Stacks 06WM, clause (5)**.

## Implementation notes

The ringed-site computation of the internal Hom out of a finite presentation is
`AlgebraicGeometry.RingedSite.exists_internalHomSheaf_iso_kernel`.

The finite presentations of Stacks 03DL(7) are presentations by universal properties, at a
module universe containing the site (`SheafOfModules.HasFiniteGlobalPresentation`), so the
computation of the internal Hom out of a presentation is made in that universe and needs no
sheafification: internal Hom carries a coproduct or a cokernel of sheaves of modules in its first
variable to a product or a kernel as soon as restriction to every slice preserves it, and
restriction to a slice preserves colimits in that universe
(`Stacks.SheafOfModules.overFunctor_preservesColimits`). The resulting kernel is brought down to
the universe of the schemes along the fully faithful, left exact universe lift.

The restriction to the small étale site is used on presheaves of modules on the slice `𝒳/y` only;
both kernels and finite products of sheaves of modules are computed on presheaves.

No sheafification hypothesis on the associated étale site of `𝒳` is needed.

## References

* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The associated étale site of `𝒳` with its structure sheaf, as a ringed site. -/
noncomputable abbrev etaleRingedSite : RingedSite.{v, w, u} where
  C := 𝒳
  J := associatedTopology B S hS p (etaleTopology B)
  O := structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)

/-- The coefficient sheaf of rings of `AlgebraicGeometry.Stack.etaleRingedSite` is the structure
sheaf of Stacks 06TV over which local quasi-coherence is stated. -/
theorem etaleRingedSite_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf (etaleRingedSite B S hS p hp).O) =
      ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) :=
  rfl

/-- The sections of the internal Hom of two étale sheaves of modules with sections in `u` are
`u`-small: over `x` they are the morphisms between the restrictions to the slice `𝒳/x`, and that
slice is essentially `u`-small by Stacks 06W0. -/
instance small_internalHomSheaf_etaleRingedSite
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (X : 𝒳ᵒᵖ) :
    Small.{u} (((etaleRingedSite B S hS p hp).internalHomSheaf F G).val.obj X) :=
  haveI := FibredSite.essentiallySmall_over B S hS p hp X.unop
  haveI := Stacks.locallySmall_presheafOfModules_of_essentiallySmall.{u}
    (ORestr (etaleRingedSite B S hS p hp).O.obj X.unop)
  inferInstanceAs (Small.{u}
    ((restrFun (etaleRingedSite B S hS p hp).O.obj X.unop).obj
        (RingedSite.valOf (etaleRingedSite B S hS p hp) F) ⟶
      (restrFun (etaleRingedSite B S hS p hp).O.obj X.unop).obj
        (RingedSite.valOf (etaleRingedSite B S hS p hp) G)))

/-- **The internal Hom `𝓗om_{𝒪_𝒳}(F, G)` of Stacks 03EM in `Mod(𝒳_étale, 𝒪_𝒳)`.** Its sections
over `x` are the morphisms `F|_{𝒳/x} ⟶ G|_{𝒳/x}`; these form a `u`-small set because the slice
`𝒳/x` is essentially `u`-small, and the internal Hom is read in the module universe `u` of `F`
and `G` through `Stacks.SheafOfModules.sheafShrink`.
`AlgebraicGeometry.Stack.etaleInternalHomIso` identifies its universe lift with the internal
Hom presheaf of Stacks 03EM. -/
noncomputable def etaleInternalHom
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) :=
  Stacks.SheafOfModules.sheafShrink.{u, max (max v w) w u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (etaleRingedSite B S hS p hp).O)
    ((etaleRingedSite B S hS p hp).internalHomSheaf F G)

/-- The internal Hom sheaf of the étale ringed site of `𝒳` is the internal Hom presheaf of
Stacks 03EM. -/
theorem etaleRingedSite_internalHomSheaf_val
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    ((etaleRingedSite B S hS p hp).internalHomSheaf F G).val =
      internalHom (structureSheaf B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj (RingedSite.valOf (etaleRingedSite B S hS p hp) F)
        (RingedSite.valOf (etaleRingedSite B S hS p hp) G) :=
  rfl

/-- The universe lift of `AlgebraicGeometry.Stack.etaleInternalHom F G` is the internal Hom
presheaf of Stacks 03EM, `internalHom 𝒪_𝒳 F G`, made a sheaf by `internalHom_isSheaf`. -/
noncomputable def etaleInternalHomIso
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    (Stacks.SheafOfModules.moduleULift.{max (max v w) w u}
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))).obj
        (etaleInternalHom B S hS p hp F G) ≅
      (etaleRingedSite B S hS p hp).internalHomSheaf F G :=
  Stacks.SheafOfModules.sheafShrinkIso.{u, max (max v w) w u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (etaleRingedSite B S hS p hp).O)
    ((etaleRingedSite B S hS p hp).internalHomSheaf F G)

/-- The restriction of Stacks 06WJ, read on the slice `𝒳/y`: a presheaf of modules on the slice
is restricted along the localization functor of Stacks 06W0 from the small étale site of the
scheme below `y`, and its scalars are moved by `AlgebraicGeometry.Stack.localStructurePresheafIso`.
The restriction of an étale sheaf of modules on `𝒳` is this applied to its restriction to the
slice, on the nose (`AlgebraicGeometry.Stack.restrictSheafToSmallEtale_obj_val`). -/
noncomputable def sliceRestrictToSmallEtale (y : 𝒳) :
    PresheafOfModules.{u} ((ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).over y).obj ⥤
      PresheafOfModules.{u}
        (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)).obj :=
  letI := isEquivalence_overPost B S hS p hp y
  PresheafOfModules.pushforward₀
      (smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y) ⋙
        (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).inv)
      ((ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).over y).obj ⋙
    PresheafOfModules.restrictScalars
      (localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
        (etaleTopology_le_topology B)).hom

/-- The restriction to the small étale site of an étale sheaf of modules on `𝒳` factors through
its restriction to the slice `𝒳/y`. -/
theorem restrictSheafToSmallEtale_obj_val (y : 𝒳)
    (F : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    ((restrictSheafToSmallEtale B E h S hS p hp y).obj F).val =
      (sliceRestrictToSmallEtale B E h S hS p hp y).obj (F.over y).val :=
  rfl

/-- The restriction from the slice `𝒳/y` to the small étale site preserves limits: on sections it
is a reindexing followed by a change of scalars. -/
instance preservesLimitsOfShape_sliceRestrictToSmallEtale (y : 𝒳) (K : Type) [SmallCategory K]
    [HasLimitsOfShape K (Type u)] :
    PreservesLimitsOfShape K (sliceRestrictToSmallEtale B E h S hS p hp y) := by
  refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun X => ?_⟩
  have := isEquivalence_overPost B S hS p hp y
  let q := smallEtaleInclusion B E h (p.obj y).left.1 (contains_base B E h S hS p y) ⋙
    (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).inv
  have : PreservesLimit (D ⋙ PresheafOfModules.evaluation ((ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B)).over y).obj (q.op.obj X))
      (ModuleCat.restrictScalars ((localStructurePresheafIso B E h S hS p hp y (etaleTopology B)
        (etaleTopology_le_topology B)).hom.app X).hom) :=
    ModuleCat.preservesLimit_restrictScalars _ _
  exact (this.preserves (isLimitOfPreserves (PresheafOfModules.evaluation ((ringStructureSheafCore
    B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).over y).obj (q.op.obj X))
      hc)).some

/-- **The internal Hom is locally quasi-coherent over an object at which the source is
finitely presented.** If the restriction of `F` to the slice `𝒳/y` is the cokernel of a map
between finite free modules, then the restriction of `𝓗om(F, G)` to the small étale site of the
scheme below `y` is the kernel of a map between finite products of copies of the restriction of
`G`, hence quasi-coherent when that restriction is. -/
theorem isQuasicoherentOnSite_restrictSheafToSmallEtale_etaleInternalHom (y : 𝒳)
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (hG : ((restrictSheafToSmallEtale B E h S hS p hp y).obj G).IsQuasicoherentOnSite)
    (hy : (F.over y).HasFiniteGlobalPresentation) :
    ((restrictSheafToSmallEtale B E h S hS p hp y).obj
      (etaleInternalHom B S hS p hp F G)).IsQuasicoherentOnSite := by
  classical
  let X := etaleRingedSite B S hS p hp
  let Rs := ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)
  let H := etaleInternalHom B S hS p hp F G
  obtain ⟨n, k, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hy
  let L := Stacks.SheafOfModules.moduleULift.{max (max v w) w u, u} (Rs.over y)
  have hL : L.FullyFaithful := Stacks.SheafOfModules.moduleULiftFullyFaithful _
  have : PreservesFiniteLimits L := Stacks.SheafOfModules.preservesFiniteLimits_moduleULift
  let IH : SheafOfModules.{max (max v w) w u} (Rs.over y) :=
    (X.over y).internalHomSheaf (F.over y).uliftForPresentation (L.obj (G.over y))
  obtain ⟨f', ⟨e'⟩⟩ : ∃ f' : (∏ᶜ fun _ : Fin n => L.obj (G.over y)) ⟶
      ∏ᶜ fun _ : Fin k => L.obj (G.over y), Nonempty (IH ≅ kernel f') :=
    RingedSite.exists_internalHomSheaf_iso_kernel (X.over y) ι hP κ hQ a b hab hb
      (L.obj (G.over y))
  -- The universe lift of the restriction of the internal Hom is the kernel of `f'`.
  let eH : L.obj (H.over y) ≅ kernel f' :=
    (SheafOfModules.overFunctor Rs y).mapIso (etaleInternalHomIso B S hS p hp F G) ≪≫
      RingedSite.internalHomSheafOverIso X y F G ≪≫
      (RingedSite.internalHomSheafULiftIso (X.over y) (F.over y) (G.over y)).symm ≪≫ e'
  let eP : ∀ m : ℕ, L.obj (∏ᶜ fun _ : Fin m => G.over y) ≅ ∏ᶜ fun _ : Fin m => L.obj (G.over y) :=
    fun m => PreservesProduct.iso L _
  let f : (∏ᶜ fun _ : Fin n => G.over y) ⟶ ∏ᶜ fun _ : Fin k => G.over y :=
    hL.preimage ((eP n).hom ≫ f' ≫ (eP k).inv)
  let eK : L.obj (kernel f) ≅ kernel f' :=
    PreservesKernel.iso L f ≪≫ kernel.mapIso _ _ (eP n) (eP k) (by simp [f])
  let eHy : H.over y ≅ kernel f := hL.preimageIso (eH ≪≫ eK.symm)
  -- Restriction to the small étale site.
  let r := sliceRestrictToSmallEtale B E h S hS p hp y
  let rs := restrictSheafToSmallEtale.{u, v, w, u} B E h S hS p hp y
  let T := rs.obj G
  let fg := SheafOfModules.forget (Rs.over y)
  let ft := SheafOfModules.forget
    (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y))
  let ε : ∀ m : ℕ, (ft.obj (∏ᶜ fun _ : Fin m => T)) ≅
      r.obj (fg.obj (∏ᶜ fun _ : Fin m => G.over y)) := fun m =>
    PreservesProduct.iso ft (fun _ : Fin m => T) ≪≫
      (PreservesProduct.iso r (fun _ : Fin m => fg.obj (G.over y))).symm ≪≫
      r.mapIso (PreservesProduct.iso fg (fun _ : Fin m => G.over y)).symm
  let φ : (∏ᶜ fun _ : Fin n => T) ⟶ ∏ᶜ fun _ : Fin k => T :=
    ⟨(ε n).hom ≫ r.map f.val ≫ (ε k).inv⟩
  let e₁ : ft.obj (rs.obj H) ≅ r.obj (fg.obj (H.over y)) :=
    eqToIso (restrictSheafToSmallEtale_obj_val B E h S hS p hp y H)
  let e₂ : r.obj (fg.obj (H.over y)) ≅ r.obj (kernel (fg.map f)) :=
    r.mapIso (fg.mapIso eHy ≪≫ PreservesKernel.iso fg f)
  let e₃ : r.obj (kernel (fg.map f)) ≅ kernel (r.map (fg.map f)) := PreservesKernel.iso r _
  let e₄ : kernel (r.map (fg.map f)) ≅ kernel (ft.map φ) :=
    kernel.mapIso _ _ (ε n).symm (ε k).symm
      (Iso.inv_hom_id_assoc (ε n) (r.map f.val ≫ (ε k).inv)).symm
  let e₅ : kernel (ft.map φ) ≅ ft.obj (kernel φ) := (PreservesKernel.iso ft φ).symm
  have hT : ∀ m : ℕ, (∏ᶜ fun _ : Fin m => T).IsQuasicoherentOnSite := fun m =>
    (SheafOfModules.isQuasicoherentOnSite _).prop_limit _ (fun _ => hG)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((SheafOfModules.fullyFaithfulForget _).preimageIso (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅)).symm
    ((SheafOfModules.isQuasicoherentOnSite _).prop_kernel φ (hT n) (hT k))

/-- **Stacks 06WM, clause (5).** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids
and let `F`, `G` be locally quasi-coherent sheaves of `𝒪_𝒳`-modules on `𝒳_étale`, with `F` of
finite presentation on `𝒳_étale`. Then the internal Hom `𝓗om_{𝒪_𝒳}(F, G)` of
`Mod(𝒳_étale, 𝒪_𝒳)` is locally quasi-coherent.

Local quasi-coherence is étale-local on the object
(`AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover`), and
every covering of an object of `𝒳_étale` is refined by arrows lying over a jointly surjective
family of étale morphisms
(`AlgebraicGeometry.Stack.exists_etaleCovering_le_of_mem_associatedTopology`);
at the members of such a refinement of a covering on which `F` is finitely presented the claim is
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictSheafToSmallEtale_etaleInternalHom`. The
hypothesis that `F` is locally quasi-coherent is part of the source's statement; the argument does
not use it. -/
@[stacks 06WM "(5): for F, G in LQCoh(𝒪_𝒳) with F of finite presentation on 𝒳_ét, the internal \
Hom 𝓗om_{𝒪_𝒳}(F, G) of Mod(𝒳_ét, 𝒪_𝒳) is locally quasi-coherent"]
theorem isLocallyQuasicoherent_etaleInternalHom
    (F G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    (_hF : IsLocallyQuasicoherent B E h S hS p hp F.val)
    (hG : IsLocallyQuasicoherent B E h S hS p hp G.val)
    (hfp : F.IsFinitePresentationOnSite) :
    IsLocallyQuasicoherent B E h S hS p hp (etaleInternalHom B S hS p hp F G).val := by
  refine (isLocallyQuasicoherent_iff B E h S hS p hp _).2 fun x => ?_
  obtain ⟨I, V, f, hcov, hpres⟩ := hfp.locally_hasFiniteGlobalPresentation x
  obtain ⟨E', hE', hle⟩ := exists_etaleCovering_le_of_mem_associatedTopology B S hS p hp _ hcov
  have hmem : ((E'.map p).map (BigFppfOver.forget B S hS)).presieve₀ ∈
      etalePrecoverage B ((BigFppfOver.forget B S hS).obj (p.obj x)) := ⟨_, rfl, hE'⟩
  have hetale : ∀ j, Etale (B.inclusion.map (p.map (E'.f j)).left) := fun j =>
    etale_of_mem_etalePrecoverage B _ hmem _ (Presieve.ofArrows.mk j)
  have hsurj := map_mem_schemeEtalePrecoverage_of_mem_etalePrecoverage B _ hmem
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hsurj
  replace hsurj := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mp hsurj
  have hpresE : ∀ j, (F.over (E'.X j)).HasFiniteGlobalPresentation := fun j => by
    obtain ⟨W, g, fi, ⟨i⟩, -⟩ := hle _ _ (Presieve.ofArrows.mk j)
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap
      F g (hpres i)
  exact isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover B E h S hS p hp x _
    (etaleInternalHom B S hS p hp F G).isSheaf E'.X E'.f hetale hsurj.1 (fun j =>
      isQuasicoherentOnSite_restrictSheafToSmallEtale_etaleInternalHom B E h S hS p hp (E'.X j)
        F G ((isLocallyQuasicoherent_iff B E h S hS p hp G).1 hG _) (hpresE j))

end AlgebraicGeometry.Stack
