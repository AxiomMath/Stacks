module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.DerivedTensorFlatRepresentative
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FlatEtaleStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.TotalTensorKFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.TotalTensorRestriction
public import StacksFrontier.Homology.PseudoCoherent.Locality
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0961 for an arbitrary scheme

Stacks Tag 0961 asks nothing of the scheme: for **any** scheme `X`, any Noetherian ring `Λ` and
any `K, L ∈ D_c^-(X_étale, Λ)`, the derived tensor product `K ⊗_Λ^L L` is again in
`D_c^-(X_étale, Λ)` — it is bounded above and all of its cohomology sheaves are constructible.
That is what this file proves.

## Main results

* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_homology_mapBifunctor_of_compactSpace` — on a
  quasi-compact quasi-separated scheme, the total tensor complex of two bounded above complexes
  with constructible cohomology, the right one having flat étale stalks, has constructible
  cohomology.
* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_homology_mapBifunctor` — the same over an
  arbitrary scheme, by Zariski descent along an affine open cover.
* `Stacks.EtaleCohomology.minus_and_isConstructible_derivedTensor_of_arbitraryScheme` —
  **Stacks 0961.**

## The argument

The source's proof is "this follows from Lemmas 0960 and 095I". Tag 0960 is available only for a
quasi-compact quasi-separated scheme, and genuinely so: its conditions (2) and (3) present a
complex by *finite* direct sums of the generators `j_{U!}\underline{Λ}`, and on a scheme which is
not quasi-compact a constructible sheaf need not be a quotient of a finite such sum. So the
argument here runs in three steps.

**A bounded above flat representative over an arbitrary scheme.** Every object of
`D^-(X_étale, Λ)` is represented by a bounded above complex of sheaves whose étale stalks are
flat `Λ`-modules, by
`AlgebraicGeometry.exists_isStrictlyLE_flat_etaleModuleStalk_of_isLE`: the generators
`j_{U!}\underline{Λ}` of Stacks 093B (2) have projective étale stalks, flat étale stalks pass to
an arbitrary coproduct, and Stacks 05T7 resolves in the same degrees. Flat étale stalks give
flatness over the constant coefficient ring sheaf
(`AlgebraicGeometry.isFlat_moduleSheafOverConstantCoefficients_of_flat_etaleModuleStalk`), which
is the form `Stacks.EtaleCohomology.IsDerivedTensorOnFlatComplexes` consumes. So for complexes
`P` and `G` representing `K` and `L` in degrees `≤ a` and `≤ b`,

`K ⊗^L_Λ L ≅ Tot(P ⊗_Λ G)`,

and `Tot(P ⊗_Λ G)` lies in degrees `≤ a + b` by
`Stacks.ConstantSheaf.isStrictlyLE_mapBifunctor`. That is the first half of the conclusion, with
the bound `a + b` rather than one read off a cover.

**The quasi-compact quasi-separated case, for the total complex.** On a quasi-compact
quasi-separated scheme the resolution engine of Tag 0960 (1) ⟹ (2) presents `P` and `G` by
*morphisms* of complexes `P' ⟶ P` and `G' ⟶ G` which are quasi-isomorphisms and whose sources have
finite affine shriek sums as terms. Those terms are flat constructible, hence constructible, so
`Tot(P' ⊗_Λ G')` has constructible terms by Tag 095I and the weak Serre property of Tag 03RZ (3);
and `Tot(P' ⊗_Λ G') ⟶ Tot(P ⊗_Λ G)` is a quasi-isomorphism, because the total tensor complex is
insensitive to a quasi-isomorphism in a variable whose opposite variable is K-flat
(`Stacks.EtaleCohomology.quasiIso_mapBifunctorMap`), and bounded above complexes with flat étale
stalks are K-flat on either side by Stacks 06YQ
(`Stacks.EtaleCohomology.kFlat_of_flat_etaleModuleStalk`). No representative has to be changed
inside the derived category, so no K-flat resolution of an arbitrary complex is needed.

**Descent to an arbitrary scheme.** Constructibility of a sheaf of `Λ`-modules is Zariski local
with no hypothesis on the scheme, by Tag 095F
(`AlgebraicGeometry.isConstructibleModuleSheaf_of_openCover`), and the affine opens of `X` are
again objects of the site (`AlgebraicGeometry.exists_affine_openCover_of_bigEtaleSite`) and are
quasi-compact and quasi-separated. Inverse image is exact, so it commutes with the cohomology of
a complex, and it commutes with the total tensor complex by
`Stacks.EtaleCohomology.smallEtaleSheafPullbackMapBifunctorIso`; flat étale stalks and
constructible cohomology both survive it, the former because the stalk of an inverse image is a
stalk of the original sheaf and the latter by Tag 095G. Only the right factor has to be flat:
the left one is replaced by a complex of affine shriek sums, whose terms are flat anyway. So the
quasi-compact quasi-separated case at each member of the cover gives the general case.

## What is assumed of the derived tensor product, and what is not

The derived tensor product enters as a bifunctor `T` on `D(X_étale, Λ)` together with
`Stacks.EtaleCohomology.IsDerivedTensorOnFlatComplexes`: the value of `T` at the classes of two
cochain complexes is the class of their total tensor complex whenever the right factor is a
bounded above complex of flat sheaves. That is not a result about `K ⊗^L_Λ L`; it is what
*identifies* `T` as the derived tensor product, and it is the `comparisonRight` field of
`Stacks.SheafOfModules.DerivedTensorProduct` — restricted to the bounded above complexes of flat
sheaves, which Tag 06YQ puts among the K-flat ones — read in the category in which
constructibility is a property of an object. `T` must enter this way: the derived tensor product
of Tag 06YU is a bifunctor on the derived category of sheaves of modules over a *ring sheaf*, and
no comparison of that category with `D(X_étale, Λ)` exists in this development, so Tag 094H's
identification is unavailable.

Neither half of the conclusion is assumed. In particular the boundedness estimate for `T` is
*proved* here rather than taken as `hbound`, and the bounded case of the tag is proved rather
than taken as `hbounded`; both come from the single complex `Tot(P ⊗_Λ G)`.

The standing instance arguments are those the small étale site of a big étale site carries
everywhere in this development — right adjointness of small étale pushforward, which is part of
the statement of Tag 03RW (3), sheafification over a slice, and additivity of the tensor product
in each variable together with the existence of total complexes, as in
`Stacks.SheafOfModules.DerivedTensorProduct`. They are quantified over every object of `B`
because the argument restricts to an affine open cover; each says something about the coefficients
and the site, and none says anything about `X`.

## The coefficient universe

The coefficient ring is `Λ : Type (max (u + 1) w)` with modules in `ModuleCat.{max (u + 1) w} Λ`,
which is the universe of Tag 095I: the small étale site of Tag 021B has objects in
`Type (u + 1)` and morphisms in `Type u`, and `ModuleCat.{s} Λ` is monoidal only for
`Λ : Type s`, so the tensor product of sheaves of `Λ`-modules exists only once the module
universe contains `u + 1` and the ring universe agrees with it.

## References

* [Stacks Project, Tag 0961](https://stacks.math.columbia.edu/tag/0961)
* [Stacks Project, Tag 0960](https://stacks.math.columbia.edu/tag/0960)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 095I](https://stacks.math.columbia.edu/tag/095I)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 093B](https://stacks.math.columbia.edu/tag/093B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.SmallEtale.moduleSheafMonoidal
  AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat
  AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat
  AlgebraicGeometry.preservesFiniteColimits_smallEtaleSheafPullback_moduleCat
  AlgebraicGeometry.additive_smallEtaleSheafPullback_moduleCat
  SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S S' : B.Scheme) (f : S' ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B S'.obj S'.property)).IsRightAdjoint]
  [∀ (S : B.Scheme) (V : SmallEtale B S.obj S.property),
    HasWeakSheafify ((SmallEtale.topology B S.obj S.property).over V)
      (ModuleCat.{max (u + 1) w} Λ)]
  [∀ S : B.Scheme, (curriedTensor
      (Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ (S : B.Scheme)
      (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ)),
    ((curriedTensor (Sheaf (SmallEtale.topology B S.obj S.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive]
  [∀ (S : B.Scheme) (K : HomologicalComplex₂
      (Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) w} Λ))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)), K.HasTotal (ComplexShape.up ℤ)]

/-! ### The quasi-compact quasi-separated case -/

/-- **On a quasi-compact quasi-separated scheme the total tensor complex of two bounded above
complexes with constructible cohomology, the right one having flat étale stalks, has
constructible cohomology.**

Tag 0960 (1) ⟹ (2) resolves each complex, in the same degrees, by one whose terms are finite
affine shriek sums; those are flat constructible, hence constructible, so the resolved total
complex has constructible terms by Tag 095I and the weak Serre property of Tag 03RZ (3). The
comparison map of total complexes is a quasi-isomorphism because both complexes are K-flat on
the relevant side, by Tag 06YQ. -/
public theorem isConstructibleModuleSheaf_homology_mapBifunctor_of_compactSpace
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (P G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ℤ) (p q : ℤ)
    (hp : CochainComplex.IsStrictlyLE P p) (hq : CochainComplex.IsStrictlyLE G q)
    (hGflat : ∀ (i : ℤ) (s : GeometricPoint X.obj), Module.Flat Λ
      ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj (G.X i)))
    (hPc : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (P.homology i))
    (hGc : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (G.homology i)) (n : ℤ) :
    IsConstructibleModuleSheaf B X Λ
      ((HomologicalComplex.mapBifunctor P G
        (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ)).homology n) := by
  have hserre := isWeakSerreClass_isConstructibleModuleSheafProperty.{u, max (u + 1) w} B X Λ
  have hfincop : ObjectProperty.IsClosedUnderFiniteCoproducts
      (isConstructibleModuleSheafProperty.{u, max (u + 1) w, max (u + 1) w} B X Λ) :=
    Stacks.ConstantSheaf.isClosedUnderFiniteCoproducts_of_isWeakSerreClass _
  have hshriek : ∀ M : Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ), IsAffineShriekSum.{u, max (u + 1) w} B X Λ M →
      IsConstructibleModuleSheaf B X Λ M ∧ ∀ s : GeometricPoint X.obj, Module.Flat Λ
        ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj M) := by
    intro M hM
    obtain ⟨m, U, hU, ⟨e⟩⟩ := hM
    have hflatconstr : IsConstructibleFlatModuleSheaf B X Λ M :=
      isConstructibleFlatModuleSheaf_congr B X Λ e.symm
        (isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated B X Λ U hU)
    refine ⟨isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ hflatconstr,
      fun s => ?_⟩
    have := etaleModuleStalk_projective_of_isConstructibleFlatModuleSheaf B X Λ M hflatconstr s
    infer_instance
  have hres := fun C r (hC : CochainComplex.IsStrictlyLE C r) hCc => by
    have := hC
    exact Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis
      (isConstructibleModuleSheafProperty.{u, max (u + 1) w, max (u + 1) w} B X Λ)
      (IsAffineShriekSum.{u, max (u + 1) w} B X Λ) C
      (coversEpis_isAffineShriekSum B X Λ) (isAffineShriekSum_zero B X Λ)
      (fun _ _ => isAffineShriekSum_biprod B X Λ)
      (fun _ _ g hg hM => by have := hg; exact isAffineShriekSum_of_iso B X Λ (asIso g) hM)
      r hCc
  obtain ⟨P', hP'LE, f, hf, hP'term⟩ := hres P p hp hPc
  obtain ⟨G', hG'LE, g, hg, hG'term⟩ := hres G q hq hGc
  have := hP'LE
  have := hG'LE
  have hqiso := quasiIso_mapBifunctorMap B X Λ f g hf hg
    (kFlat_of_flat_etaleModuleStalk B X Λ G q hGflat)
    (kFlatLeft_of_flat_etaleModuleStalk B X Λ P' p
      (fun i s => (hshriek _ (hP'term i)).2 s))
  have hterm : ∀ m : ℤ, IsConstructibleModuleSheaf B X Λ
      ((HomologicalComplex.mapBifunctor P' G' (curriedTensor _) (ComplexShape.up ℤ)).X m) := by
    intro m
    exact Stacks.ConstantSheaf.prop_mapBifunctor_of_isStrictlyLE (curriedTensor _) P' G' p q
      (isConstructibleModuleSheafProperty.{u, max (u + 1) w, max (u + 1) w} B X Λ)
      (fun a' b' => isConstructibleModuleSheaf_tensor B X Λ _ _
        (hshriek _ (hP'term a')).1 (hshriek _ (hG'term b')).1) m
  set Q := isConstructibleModuleSheafProperty.{u, max (u + 1) w, max (u + 1) w} B X Λ with hQ
  set M' := HomologicalComplex.mapBifunctor P' G' (curriedTensor
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
    (ComplexShape.up ℤ) with hM'
  have hcyc : Q (M'.cycles n) :=
    Q.prop_of_isLimit_kernelFork (M'.cyclesIsKernel n (n + 1) (by simp)) (hterm n)
      (hterm (n + 1))
  have hhom : Q (M'.homology n) :=
    Q.prop_of_isColimit_cokernelCofork (M'.homologyIsCokernel (n - 1) n (by simp))
      (hterm (n - 1)) hcyc
  have := hqiso
  exact Q.prop_of_iso (asIso (HomologicalComplex.homologyMap
    (HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (ComplexShape.up ℤ)) n)) hhom

/-! ### Descent to an arbitrary scheme -/

/-- **The cohomology sheaves of the total tensor complex of two bounded above complexes with
constructible cohomology, the right one having flat étale stalks, are constructible**, over an
arbitrary scheme.

Constructibility is Zariski local by Tag 095F, the affine opens of `X` are again objects of the
site and are quasi-compact and quasi-separated, inverse image commutes with the cohomology of a
complex and with the total tensor complex, and flat étale stalks and constructible cohomology
both survive it. Flatness is needed of the right factor alone: the left factor is replaced by a
complex of affine shriek sums, whose terms have flat étale stalks for free. -/
public theorem isConstructibleModuleSheaf_homology_mapBifunctor (X : B.Scheme)
    (P G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ℤ) (p q : ℤ)
    (hp : CochainComplex.IsStrictlyLE P p) (hq : CochainComplex.IsStrictlyLE G q)
    (hGflat : ∀ (i : ℤ) (s : GeometricPoint X.obj), Module.Flat Λ
      ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj (G.X i)))
    (hPc : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (P.homology i))
    (hGc : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (G.homology i)) (n : ℤ) :
    IsConstructibleModuleSheaf B X Λ
      ((HomologicalComplex.mapBifunctor P G
        (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ)).homology n) := by
  let _ : HasProducts.{u} (ModuleCat.{max (u + 1) w} Λ) := fun _ =>
    ModuleCat.hasLimitsOfShape
  obtain ⟨I, W, jj, hj, haff, hcov⟩ := exists_affine_openCover_of_bigEtaleSite B X
  refine isConstructibleModuleSheaf_of_openCover B Λ X _ W jj hj hcov (fun k => ?_)
  have haffk := haff k
  have hck : CompactSpace (W k).obj := Scheme.compactSpace_of_isAffine _
  have hqk : QuasiSeparatedSpace (W k).obj := quasiSeparatedSpace_of_isAffine _
  set Phi := (smallEtaleBaseChange B (jj k)).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
    (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B (W k).obj (W k).property) with hPhi
  have hLE : ∀ (C : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ)) ℤ) (b : ℤ), CochainComplex.IsStrictlyLE C b →
      CochainComplex.IsStrictlyLE ((Phi.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) b := by
    intro C b hb
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact Phi.map_isZero ((C.isStrictlyLE_iff b).mp hb i hi)
  have hhom : ∀ (C : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ)) ℤ) (i : ℤ),
      ((Phi.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology i ≅
        Phi.obj (C.homology i) :=
    fun C i => (StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso
      Phi i).app C
  have hCck := fun C (hC : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (C.homology i)) (i : ℤ) =>
    isConstructibleModuleSheaf_congr B Λ (W k) (hhom C i).symm
      (isConstructibleModuleSheaf_pullback B Λ (jj k) _ (hC i))
  have hGfk : ∀ (i : ℤ) (s : GeometricPoint (W k).obj), Module.Flat Λ
      ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B (W k) Λ s).obj
        (((Phi.mapHomologicalComplex (ComplexShape.up ℤ)).obj G).X i)) := fun i s =>
    flat_etaleModuleStalk_smallEtaleSheafPullback.{u, max (u + 1) w, max (u + 1) w}
      B Λ (jj k) (G.X i) (fun t => hGflat i t) s
  have hconstr := isConstructibleModuleSheaf_homology_mapBifunctor_of_compactSpace B Λ (W k)
    _ _ p q (hLE P p hp) (hLE G q hq) hGfk (hCck P hPc) (hCck G hGc) n
  refine isConstructibleModuleSheaf_congr B Λ (W k) ?_ hconstr
  exact ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
    (smallEtaleSheafPullbackMapBifunctorIso B Λ (jj k) P G)).symm ≪≫ hhom _ n

/-! ### Stacks 0961 -/

variable (X : B.Scheme)

variable (T : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ⥤
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ⥤
    DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)))

/-- **Stacks 0961.** Let `X` be a scheme, `Λ` a Noetherian ring and `K, L ∈ D_c^-(X_étale, Λ)`.
Then `K ⊗_Λ^L L` is in `D_c^-(X_étale, Λ)`: it is bounded above, and all of its cohomology
sheaves are constructible.

Nothing is asked of the scheme, and no part of the conclusion is assumed. The only thing asked of
the derived tensor product `T` is `hcomp`, which says that `T` *is* the derived tensor product:
its value on a pair of complexes whose right member is a bounded above complex of flat sheaves is
the total tensor complex. Both halves of the conclusion come from one complex `Tot(P ⊗_Λ G)`,
where `P` and `G` are the bounded above representatives with flat étale stalks of
`AlgebraicGeometry.exists_isStrictlyLE_flat_etaleModuleStalk_of_isLE` — boundedness above with
the bound `a + b`, and constructibility of the cohomology sheaves by
`Stacks.EtaleCohomology.isConstructibleModuleSheaf_homology_mapBifunctor`. -/
@[stacks 0961 "for an arbitrary scheme: both halves of the conclusion, the boundedness estimate \
  for the derived tensor product and the constructible case alike, from the bounded above \
  representative with flat etale stalks of Stacks 05T7 and 093B (2), the quasi-compact \
  quasi-separated case of Stacks 0960 and 095I, and Zariski descent for constructibility, \
  Stacks 095F"]
public theorem minus_and_isConstructible_derivedTensor_of_arbitraryScheme
    (hcomp : IsDerivedTensorOnFlatComplexes.{u, w} B X Λ T)
    (K L : DerivedCategory.Minus (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsConstructible B X Λ K.obj) (hL : IsConstructible B X Λ L.obj) :
    (DerivedCategory.TStructure.t (C := Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))).minus ((T.obj K.obj).obj L.obj) ∧
      IsConstructible B X Λ ((T.obj K.obj).obj L.obj) := by
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨b, hb⟩ := L.property
  obtain ⟨P, hPLE, hPflat, ⟨eP⟩⟩ :=
    exists_isStrictlyLE_flat_etaleModuleStalk_of_isLE.{u, max (u + 1) w} B X Λ K.obj a ha
  obtain ⟨G, hGLE, hGflat, ⟨eG⟩⟩ :=
    exists_isStrictlyLE_flat_etaleModuleStalk_of_isLE.{u, max (u + 1) w} B X Λ L.obj b hb
  obtain ⟨e⟩ := hcomp P G b hGLE (fun i =>
    isFlat_moduleSheafOverConstantCoefficients_of_flat_etaleModuleStalk.{u, max (u + 1) w,
      max (u + 1) w} B X Λ (G.X i) (hGflat i))
  have hPc : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (P.homology i) := fun i =>
    isConstructibleModuleSheaf_congr B Λ X
      (((DerivedCategory.homologyFunctor _ i).mapIso eP).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors _ i).app P)) (hK i)
  have hGc : ∀ i : ℤ, IsConstructibleModuleSheaf B X Λ (G.homology i) := fun i =>
    isConstructibleModuleSheaf_congr B Λ X
      (((DerivedCategory.homologyFunctor _ i).mapIso eG).symm ≪≫
        ((DerivedCategory.homologyFunctorFactors _ i).app G)) (hL i)
  set M := HomologicalComplex.mapBifunctor P G (curriedTensor
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
    (ComplexShape.up ℤ) with hM
  have etot : (T.obj K.obj).obj L.obj ≅ DerivedCategory.Q.obj M :=
    (T.mapIso eP).symm.app L.obj ≪≫
      (T.obj (DerivedCategory.Q.obj P)).mapIso eG.symm ≪≫ e
  have hMLE : CochainComplex.IsStrictlyLE M (a + b) := by
    have := hPLE
    have := hGLE
    exact Stacks.ConstantSheaf.isStrictlyLE_mapBifunctor _ P G a b
  refine ⟨⟨a + b, ?_⟩, fun i => ?_⟩
  · have := hMLE
    have h1 : (DerivedCategory.Q.obj M).IsLE (a + b) := inferInstance
    exact DerivedCategory.TStructure.t.isLE_of_iso etot.symm (a + b)
  · refine isConstructibleModuleSheaf_congr B Λ X ?_
      (isConstructibleModuleSheaf_homology_mapBifunctor B Λ X P G a b hPLE hGLE hGflat
        hPc hGc i)
    exact (((DerivedCategory.homologyFunctorFactors _ i).app M).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso etot.symm)

end Stacks.EtaleCohomology

end
