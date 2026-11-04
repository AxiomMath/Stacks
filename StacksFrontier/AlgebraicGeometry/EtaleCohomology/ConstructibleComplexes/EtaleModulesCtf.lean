module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedStalkPerfection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison

/-!
# Constructible complexes of finite Tor dimension on Mathlib's small étale site

Let `X` be a scheme and `Λ` a ring, not necessarily commutative. This file defines the category
`D_ctf(X_étale, Λ)` for sheaves of `Λ`-modules on Mathlib's small étale site of `X` — the
category `Stacks.EtaleCohomology.EtaleModules Λ X` on which cohomology with compact support and
the étale stalks of the trace formula live — and proves that the stalks of its objects are
perfect complexes of `Λ`-modules.

## Main definitions

* `Stacks.EtaleCohomology.IsConstructibleFlatEtaleModule` — a sheaf of `Λ`-modules on Mathlib's
  small étale site of `X` is constructible flat: its transport to the small étale site of
  Stacks 021B is constructible flat in the sense of
  `AlgebraicGeometry.IsConstructibleFlatModuleSheaf`.
* `Stacks.EtaleCohomology.IsCtf` — an object of `D(X_étale, Λ)` lies in `D_ctf(X_étale, Λ)`: it
  is represented by a bounded complex of constructible flat sheaves of `Λ`-modules.

## Main results

* `Stacks.EtaleCohomology.isCtf_iff_isRepresentedByConstructibleFlatComplex` — membership
  transports across the identification `AlgebraicGeometry.SmallEtale.sheafEquiv` of the two
  presentations of the small étale site, to condition (2) of [Stacks, Tag 03TT] there.
* `Stacks.EtaleCohomology.isPerfect_stalkComplex_of_isCtf` — **the stalks of an object of
  `D_ctf(X_étale, Λ)` are perfect** ([Stacks, Tag 03TR] and the direction (1) ⟹ (2) of
  [Stacks, Tag 03TT] as the trace formula uses them, [Stacks, Tag 03TY]): for a cochain complex
  `K` of sheaves of `Λ`-modules whose class lies in `D_ctf(X_étale, Λ)`, the stalk complex `K_x̄`
  at every geometric point is a perfect complex of `Λ`-modules.

## Implementation notes

**Which definition.** The source defines `D_ctf(X_étale, Λ)`, Tag 03TQ, for a Noetherian
(commutative) ring `Λ`, as the objects of `D_c(X_étale, Λ)` of locally finite Tor dimension, and
Tag 03TT shows that on a quasi-compact and quasi-separated scheme these are exactly the objects
represented by a finite complex of constructible flat sheaves. The trace formula, Tags 03TV, 03TX,
03UG and 03V3, takes `Λ` to be a *finite and possibly noncommutative* ring (Tag 03SZ fixes all
modules to be left modules and works in `Λ^natural`). For such a ring only the second description
is available in this development: Tor dimension against sheaves of right modules over a
noncommutative constant ring sheaf has no formulation here, the ringed sites of
`AlgebraicGeometry.RingedSite` having a structure sheaf valued in commutative rings. The second
description is also how [SGA 4½, Rapport 4.6] *defines* `D_ctf`. It is therefore the definition
adopted here, at the source's generality: `Λ` is an arbitrary ring. Its agreement with the
Tor-dimension definition `Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory` of
Tag 03TQ, for a Noetherian commutative ring and a quasi-compact quasi-separated scheme, is
Tag 03TT.

**Which site.** Constructibility is formulated in this development on the small étale site of
Stacks 021B, `AlgebraicGeometry.SmallEtale B X.obj X.property`, of an object `X` of a big étale
site `B`; that is also the source's convention, the small étale site of Stacks 021B being defined
relative to a big étale site. Cohomology with compact support and the étale stalks live on
Mathlib's small étale site `X.obj.smallEtaleTopology`. The two have equivalent categories of
sheaves, `AlgebraicGeometry.SmallEtale.sheafEquiv`, and a sheaf on Mathlib's site is constructible
flat when its transport is: no second notion of constructibility is introduced.

**Coefficient side conditions.** Constructibility carries two instance hypotheses on the bounded
site — direct images between small étale sites are right adjoints and the localizations admit weak
sheafification — which
`AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat` and
`AlgebraicGeometry.SmallEtale.hasWeakSheafify_over_moduleCat` discharge for a commutative ring.
Their proofs use no commutativity; they are restated here for an arbitrary ring at the coefficient
universe `max (u + 1) r` of `Stacks.EtaleCohomology.EtaleModules`, so that the definitions below
carry no instance hypotheses at all.

## References

* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 03TR](https://stacks.math.columbia.edu/tag/03TR)
* [Stacks Project, Tag 03SZ](https://stacks.math.columbia.edu/tag/03SZ)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- The forgetful functor from `Λ`-modules at the coefficient universe `max (u + 1) r` preserves
filtered colimits indexed by the universe `u + 1`. -/
private theorem preservesFilteredColimitsOfSize_forget_moduleCat :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget (ModuleCat.{max (u + 1) r} Λ)) := by
  let : PreservesColimits (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r, r, max (u + 1) r, max (u + 1) r} Λ
  let : PreservesFilteredColimits (forget (ModuleCat.{max (u + 1) r} Λ)) :=
    comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat) (forget AddCommGrpCat)
  exact preservesFilteredColimitsOfSize_shrink.{u + 1, r, u + 1, r} _

/-- **Weak sheafification on the localizations of a small étale site, with coefficients in
modules over an arbitrary ring**, at the coefficient universe `max (u + 1) r`. The proof is that
of `AlgebraicGeometry.SmallEtale.hasWeakSheafify_over_moduleCat`, which uses no commutativity. -/
public theorem hasWeakSheafify_over_moduleCat_ring (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ) := by
  have := preservesFilteredColimitsOfSize_forget_moduleCat.{u, r} Λ
  infer_instance

/-- **The direct image of sheaves of modules over an arbitrary ring between small étale sites is
a right adjoint**, at the coefficient universe `max (u + 1) r`. The proof is that of
`AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat`, which uses no
commutativity. -/
public theorem isRightAdjoint_smallEtalePushforward_moduleCat_ring (S T : B.Scheme)
    (g : T ⟶ S) :
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint := by
  have := preservesFilteredColimitsOfSize_forget_moduleCat.{u, r} Λ
  infer_instance

end AlgebraicGeometry.SmallEtale

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

/-- The identification of the sheaves of `Λ`-modules on Mathlib's small étale site of `X` with
those on the small étale site of Stacks 021B, in the direction from Mathlib's site. -/
public abbrev etaleModulesToSmallEtale :
    EtaleModules.{u, r} Λ X.obj ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ) :=
  (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).inverse

/-- **A constructible flat sheaf of `Λ`-modules on Mathlib's small étale site.** Its transport to
the small étale site of Stacks 021B is constructible flat: on a finite constructible
stratification of every affine open it is locally constant with finite projective values. -/
public def IsConstructibleFlatEtaleModule (F : EtaleModules.{u, r} Λ X.obj) : Prop :=
  let := SmallEtale.hasSheafify_moduleCat.{u, r, r} B X Λ
  IsConstructibleFlatModuleSheaf.{u, max (u + 1) r, r} B X Λ
    ((etaleModulesToSmallEtale B X Λ).obj F)

/-- Constructible flatness on Mathlib's small étale site is invariant under isomorphism. -/
public theorem IsConstructibleFlatEtaleModule.of_iso {F G : EtaleModules.{u, r} Λ X.obj}
    (e : F ≅ G) (hF : IsConstructibleFlatEtaleModule B X Λ F) :
    IsConstructibleFlatEtaleModule B X Λ G :=
  isConstructibleFlatModuleSheaf_congr B X Λ ((etaleModulesToSmallEtale B X Λ).mapIso e) hF

/-- **Condition (2) of Tag 03TT on Mathlib's small étale site.** An object of the derived
category of sheaves of `Λ`-modules on Mathlib's small étale site of `X` is represented by a
bounded complex of constructible flat sheaves of `Λ`-modules. -/
public def IsRepresentedByConstructibleFlatEtaleComplex
    (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)) : Prop :=
  ∃ (C : CochainComplex (EtaleModules.{u, r} Λ X.obj) ℤ) (a b : ℤ),
    C.IsStrictlyGE a ∧ C.IsStrictlyLE b ∧
      (∀ i : ℤ, IsConstructibleFlatEtaleModule B X Λ (C.X i)) ∧
      Nonempty (DerivedCategory.Q.obj C ≅ K)

/-- Condition (2) of Tag 03TT is invariant under isomorphism. -/
public theorem IsRepresentedByConstructibleFlatEtaleComplex.of_iso
    {K L : DerivedCategory (EtaleModules.{u, r} Λ X.obj)} (e : K ≅ L)
    (hK : IsRepresentedByConstructibleFlatEtaleComplex B X Λ K) :
    IsRepresentedByConstructibleFlatEtaleComplex B X Λ L := by
  obtain ⟨C, a, b, ha, hb, hC, ⟨e'⟩⟩ := hK
  exact ⟨C, a, b, ha, hb, hC, ⟨e' ≪≫ e⟩⟩

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- The derived inverse image `f^{-1}` along a morphism of schemes, on unbounded derived
categories of sheaves of `Λ`-modules on Mathlib's small étale sites. Inverse image is exact, so
it is the functor induced degreewise. `Λ` is any ring, not necessarily commutative; for
commutative `Λ` this is `Stacks.EtaleCohomology.etaleModuleDerivedInverseImage`. -/
public abbrev etaleModuleRingDerivedInverseImage {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    DerivedCategory (EtaleModules.{u, r} Λ Z) ⥤ DerivedCategory (EtaleModules.{u, r} Λ Y) :=
  (etaleModuleInverseImage.{u, r} Λ f).mapDerivedCategory

/-- **`D_ctf(X_étale, Λ)` on Mathlib's small étale site.** An object `K` of the derived category of
sheaves of `Λ`-modules on Mathlib's small étale site of `X` lies in `D_ctf(X_étale, Λ)` if for
every quasi-compact and quasi-separated scheme `W` of the big étale site and every morphism
`f : W ⟶ X` the inverse image `f^{-1}K` is represented by a bounded complex of constructible flat
sheaves of `Λ`-modules on `W`.

The ring `Λ` is arbitrary, as in the trace formula, where it is finite and possibly
noncommutative. For a Noetherian commutative ring this is the category of Tag 03TQ: an object of
Tag 03TQ pulls back to one (Tag 0963) and on a quasi-compact and quasi-separated scheme is
represented as required (Tag 03TT); conversely membership of Tag 03TQ is local, and the affine
opens of `X` are quasi-compact and quasi-separated. On a quasi-compact and quasi-separated `X`
itself the condition is condition (2) of Tag 03TT for `K`. -/
public def IsCtf (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)) : Prop :=
  ∀ (W : B.Scheme) (f : W ⟶ X), CompactSpace W.obj → QuasiSeparatedSpace W.obj →
    IsRepresentedByConstructibleFlatEtaleComplex B W Λ
      ((etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map f)).obj K)

/-- Membership of `D_ctf(X_étale, Λ)` is invariant under isomorphism. -/
public theorem IsCtf.of_iso {K L : DerivedCategory (EtaleModules.{u, r} Λ X.obj)} (e : K ≅ L)
    (hK : IsCtf B X Λ K) : IsCtf B X Λ L := fun W f hc hq =>
  (hK W f hc hq).of_iso B W Λ ((etaleModuleRingDerivedInverseImage.{u, r} Λ _).mapIso e)

/-! ### The stalks of an object of `D_ctf(X_étale, Λ)` are perfect -/

/-- Filtered colimits of `Λ`-modules indexed by the universe of the small étale site are exact;
this is what makes the étale stalk functor left exact. -/
theorem etaleModules_ab5OfSize : AB5OfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ) :=
  AB5OfSize_shrink.{u, u, max (u + 1) r, max (u + 1) r} _

attribute [local instance] etaleModules_ab5OfSize

/-- The étale stalk functor at a geometric point `s` of `X`, on sheaves of `Λ`-modules on Mathlib's
small étale site: the fibre functor of the point `AlgebraicGeometry.Scheme.pointSmallEtale`. -/
public abbrev etaleModuleStalk (s : GeometricPoint X.obj) :
    EtaleModules.{u, r} Λ X.obj ⥤ ModuleCat.{max (u + 1) r} Λ :=
  (Scheme.pointSmallEtale s.hom).sheafFiber

/-- The étale stalk functor is additive, being left exact. -/
public instance etaleModuleStalk_additive (s : GeometricPoint X.obj) :
    (etaleModuleStalk.{u, r} B X Λ s).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The étale stalk on Mathlib's small étale site is the stalk of the transported sheaf on the
small étale site of Stacks 021B. -/
public def etaleModuleStalkIsoTransport (s : GeometricPoint X.obj) :
    etaleModuleStalk.{u, r} B X Λ s ≅
      etaleModulesToSmallEtale B X Λ ⋙ etaleModuleStalkFunctor.{u, max (u + 1) r, r} B X Λ s :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sheafEquivCompSheafFiberIso.{u, max (u + 1) r, r} B X Λ s)

/-- The derived étale stalk at a geometric point, on Mathlib's small étale site. -/
public abbrev derivedEtaleModuleStalk (s : GeometricPoint X.obj) :
    DerivedCategory (EtaleModules.{u, r} Λ X.obj) ⥤ DerivedCategory (ModuleCat.{max (u + 1) r} Λ) :=
  (etaleModuleStalk.{u, r} B X Λ s).mapDerivedCategory

/-- **The stalks of a bounded complex of constructible flat sheaves are perfect**, on Mathlib's
small étale site: for an object of `D(X_étale, Λ)` satisfying condition (2) of Tag 03TT, the
derived stalk at every geometric point is a perfect complex of `Λ`-modules (Tag 03TR). -/
public theorem isPerfect_derivedEtaleModuleStalk_of_isRepresentedByConstructibleFlatEtaleComplex
    (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj))
    (hK : IsRepresentedByConstructibleFlatEtaleComplex B X Λ K) (s : GeometricPoint X.obj) :
    StacksDraft.Perfect.IsPerfect ((derivedEtaleModuleStalk.{u, r} B X Λ s).obj K) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, r, r} B X Λ
  obtain ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩ := hK
  let ρ := etaleModulesToSmallEtale B X Λ
  let C' := (ρ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  have hbounded : CochainComplex.plus _ C' ∧ CochainComplex.minus _ C' := by
    have : CochainComplex.IsStrictlyGE C' a := by
      rw [CochainComplex.isStrictlyGE_iff]
      exact fun i hi => ρ.map_isZero (C.isZero_of_isStrictlyGE a i hi)
    have : CochainComplex.IsStrictlyLE C' b := by
      rw [CochainComplex.isStrictlyLE_iff]
      exact fun i hi => ρ.map_isZero (C.isZero_of_isStrictlyLE b i hi)
    exact ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩
  let eC : ((etaleModuleStalk.{u, r} B X Λ s).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
      etaleModuleStalkComplex.{u, max (u + 1) r, r} B X Λ s C' :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (etaleModuleStalkIsoTransport.{u, r} B X Λ s).app (C.X i))
      (fun i j _ => ((etaleModuleStalkIsoTransport.{u, r} B X Λ s).hom.naturality (C.d i j)).symm)
  exact StacksDraft.Perfect.isPerfect_of_iso
    ((derivedEtaleModuleStalk.{u, r} B X Λ s).mapIso e.symm ≪≫
      (etaleModuleStalk.{u, r} B X Λ s).mapDerivedCategoryFactors.app C ≪≫
      DerivedCategory.Q.mapIso eC)
    (stalk_isPerfect_of_isConstructibleFlatModuleSheaf.{u, max (u + 1) r, r} B X Λ C' hbounded hC s)

/-- **The stalks of an object of `D_ctf(X_étale, Λ)` are perfect.** For `K` in `D_ctf(X_étale, Λ)`
and a geometric point `s` of `X`, the derived stalk `K_s` is a perfect complex of `Λ`-modules.

This is what the source reads off membership of `D_ctf` in Tags 03TY and 03UG, through Tag 03TT and
Tag 03TR. An affine open `W` of `X` through the image of `s` is quasi-compact and quasi-separated,
so `K|_W` is represented by a bounded complex of constructible flat sheaves; the stalk of `K` at
`s` is the stalk of `K|_W` at the lift of `s` to `W`, and the stalks of such a complex are perfect
by `isPerfect_derivedEtaleModuleStalk_of_isRepresentedByConstructibleFlatEtaleComplex`. -/
public theorem isPerfect_derivedEtaleModuleStalk_of_isCtf
    (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)) (hK : IsCtf B X Λ K)
    (s : GeometricPoint X.obj) :
    StacksDraft.Perfect.IsPerfect ((derivedEtaleModuleStalk.{u, r} B X Λ s).obj K) := by
  obtain ⟨_, ⟨W₀, hW, rfl⟩, hxW, -⟩ :=
    X.obj.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (s.hom.base default)) isOpen_univ
  let W : X.obj.Opens := W₀
  let W' : B.Scheme :=
    B.obj W.toScheme (lt_of_le_of_lt (Scheme.size_coe_opens_le X.obj W) X.property)
  let j : W' ⟶ X := ObjectProperty.homMk W.ι
  have : IsAffine W'.obj := hW
  have hrange : Set.range s.hom.base ⊆ Set.range W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let t : GeometricPoint W'.obj :=
    { residueField := s.residueField, hom := IsOpenImmersion.lift W.ι s.hom hrange }
  have ht : t.hom ≫ B.inclusion.map j = s.hom := IsOpenImmersion.lift_fac W.ι s.hom hrange
  have := etaleModuleStalk_additive.{u, r} B W' Λ t
  let g := B.inclusion.map j
  -- the stalk of `g⁻¹ F` at `t` is the stalk of `F` at `t ≫ g = s`
  let e₁ : etaleModuleInverseImage.{u, r} Λ g ⋙ etaleModuleStalk.{u, r} B W' Λ t ≅
      (Scheme.pointSmallEtale (t.hom ≫ g)).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ) :=
    ((Scheme.pointSmallEtale t.hom).sheafFiberComapIso (smallEtaleBaseChange g)
        (coverPreserving_smallEtaleBaseChange g) (ModuleCat.{max (u + 1) r} Λ)).symm ≪≫
      (GrothendieckTopology.Point.sheafFiberIsoOfFiberIso (A := ModuleCat.{max (u + 1) r} Λ)
        (Scheme.pointSmallEtale (t.hom ≫ g))
        ((Scheme.pointSmallEtale t.hom).comap (smallEtaleBaseChange g)
          (coverPreserving_smallEtaleBaseChange g)) (pointSmallEtaleComapFiberIso g t.hom)).symm
  let e₂ : (Scheme.pointSmallEtale (t.hom ≫ g)).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ) ≅
      etaleModuleStalk.{u, r} B X Λ s :=
    eqToIso (by rw [ht])
  let e := e₁ ≪≫ e₂
  obtain ⟨C, ⟨eC⟩⟩ : ∃ C : CochainComplex (EtaleModules.{u, r} Λ X.obj) ℤ,
      Nonempty (DerivedCategory.Q.obj C ≅ K) := ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  let eD : ((etaleModuleStalk.{u, r} B X Λ s).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ≅
      ((etaleModuleStalk.{u, r} B W' Λ t).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) :=
    HomologicalComplex.Hom.isoOfComponents (fun i => (e.app (C.X i)).symm)
      (fun i j _ => (e.inv.naturality (C.d i j)).symm)
  exact StacksDraft.Perfect.isPerfect_of_iso
    ((derivedEtaleModuleStalk.{u, r} B X Λ s).mapIso eC.symm ≪≫
      (etaleModuleStalk.{u, r} B X Λ s).mapDerivedCategoryFactors.app C ≪≫
      DerivedCategory.Q.mapIso eD ≪≫
      ((etaleModuleStalk.{u, r} B W' Λ t).mapDerivedCategoryFactors.app _).symm ≪≫
      (derivedEtaleModuleStalk.{u, r} B W' Λ t).mapIso
        (((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.app C).symm ≪≫
          (etaleModuleRingDerivedInverseImage.{u, r} Λ g).mapIso eC))
    (isPerfect_derivedEtaleModuleStalk_of_isRepresentedByConstructibleFlatEtaleComplex
      B W' Λ _ (hK W' j inferInstance inferInstance) t)

/-- **The stalk complexes of a complex in `D_ctf(X_étale, Λ)` are perfect.** For a cochain complex
`K` of sheaves of `Λ`-modules on Mathlib's small étale site of `X` whose class lies in
`D_ctf(X_étale, Λ)`, the stalk complex `K_s`, taken degreewise, is a perfect complex of
`Λ`-modules at every geometric point `s`. The stalk functor is exact, so the stalk complex
computes the derived stalk. -/
public theorem isPerfect_stalkComplex_of_isCtf
    (K : CochainComplex (EtaleModules.{u, r} Λ X.obj) ℤ)
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K))
    (s : GeometricPoint X.obj) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((etaleModuleStalk.{u, r} B X Λ s).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  StacksDraft.Perfect.isPerfect_of_iso
    ((etaleModuleStalk.{u, r} B X Λ s).mapDerivedCategoryFactors.app K).symm
    (isPerfect_derivedEtaleModuleStalk_of_isCtf B X Λ _ hK s)

end Stacks.EtaleCohomology

end
