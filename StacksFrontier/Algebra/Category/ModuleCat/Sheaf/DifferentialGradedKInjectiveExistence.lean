module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAcyclicNullHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAcyclicSmallSubmodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedSumsProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE

/-!
# K-injective resolutions of differential graded modules on a site

Let `X` be a ringed site and let `A` be a sheaf of differential graded algebras on it. This
file proves **Tag 0FSY**, that a *set* of monomorphisms of acyclic right differential graded
`A`-modules detects the modules that are both K-injective and graded injective, then
**Tag 0FT0**, that every right differential graded `A`-module admits a functorial
quasi-isomorphism into a graded injective K-injective one, and from it **Tag 0FT9**, the direct
sums and products of the derived category.

## Main results

* `SheafOfModules.DifferentialGradedModule.exists_setIndexed_acyclic_monomorphisms_iff` is
  **Tag 0FSY**: there is a set-indexed family of monomorphisms of acyclic right differential
  graded modules across which a module has the extension property exactly when it is
  K-injective and graded injective.
* `SheafOfModules.DifferentialGradedModule.nonempty_gradedInjectiveKInjectiveResolution` is
  **Tag 0FT0**: the functorial graded injective K-injective resolution exists.
* `SheafOfModules.DifferentialGradedModule.hasKInjectiveResolutions_dg`: every right
  differential graded module admits a quasi-isomorphism into a graded injective K-injective one.
* `SheafOfModules.DifferentialGradedModule.derivedCategory_sumsAndProducts` is **Tag 0FT9**,
  with no side condition: the derived category has direct sums and products, the direct sums are
  those of the right differential graded modules, and the products are those of the K-injective
  ones. Its parts are also available separately, under the sheafification conditions of the
  derived category, as
  `SheafOfModules.DifferentialGradedModule.derivedCategory_hasProducts_and_hasCoproducts`,
  `….isColimit_derivedCofanOfModules_dg`, `….isLimit_derivedFanOfKInjectives_dg` and
  `….isLimit_derivedFanOfKInjectiveResolutions_dg`.

## Implementation notes

**The family.** It is the disjoint union of two set-indexed families. The first is the family
of Tag 0FSS, which detects graded injectivity. The second is indexed by the set of Tag 0FST:
nonzero acyclic modules `Ms s` such that every nonzero acyclic module receives a monomorphism
from one of them; the monomorphism attached to `s` is the inclusion of `Ms s` into the cone on
its identity, which is acyclic and null-homotopic, so the extension property across it says
exactly that every morphism `Ms s ⟶ I` is null-homotopic.

**Why that suffices for K-injectivity.** Null-homotopy of the morphisms out of the members of
the second family propagates to every acyclic module by
`homotopic_zero_of_acyclic_of_detectingFamily`, the transfinite argument following Tag 079L,
which uses the smallness of Tag 0FST's family.

**Tag 0FT0.** The resolution functor is `exists_gradedInjectiveKInjectiveResolution`, the
small-object argument of Tag 0FT0, applied to that family.

**Tag 0FT9.** Part (3) is about products of K-injective modules, with no graded injectivity:
the morphisms of the derived category into a K-injective module are its homotopy classes,
`bijective_toDerivedCategory_map_of_isKInjective`, because the cone arguments of Tag 0FSX do not
use graded injectivity. The derived category is formed under the two conditions
`HasSheafify X.J AddCommGrpCat` and `X.J.WEqualsLocallyBijective AddCommGrpCat`, which make
sheaves of modules abelian; in a universe containing the site both hold, by transport from a
small model of the site, and `ringedSite_hasSheafify_addCommGrpCat` and
`ringedSite_wEqualsLocallyBijective_addCommGrpCat` record that, as local instances.

## References

* [Stacks Project, Tag 0FSY](https://stacks.math.columbia.edu/tag/0FSY)
* [Stacks Project, Tag 0FT0](https://stacks.math.columbia.edu/tag/0FT0)
* [Stacks Project, Tag 0FSS](https://stacks.math.columbia.edu/tag/0FSS)
* [Stacks Project, Tag 0FST](https://stacks.math.columbia.edu/tag/0FST)
* [Stacks Project, Tag 0FT9](https://stacks.math.columbia.edu/tag/0FT9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m

namespace SheafOfModules.DifferentialGradedModule

section Conditions

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  [HasWeakSheafify X.J (Type max u v w)]
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- For a sheaf of differential graded algebras `A` on a ringed site there is a *set* `Idx` and,
for each `r : Idx`, a monomorphism `Ms r ⟶ Ms' r` of acyclic right differential graded
`A`-modules, such that a right differential graded `A`-module `I` is K-injective (Tag 0FSU) and
graded injective (Tag 0FSP) if and only if every morphism `Ms r ⟶ I` extends along
`Ms r ⟶ Ms' r` to a morphism `Ms' r ⟶ I`. The index type lies in the universe of the modules
themselves. -/
@[stacks 0FSY "the index type in the module universe, so that the family is a set"]
theorem exists_setIndexed_acyclic_monomorphisms_iff
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ∃ (Idx : Type max u v w)
      (Ms Ms' : Idx → DifferentialGradedModule.{u, v, max u v w} A)
      (i : ∀ r, Ms r ⟶ Ms' r),
      (∀ r, Mono (i r)) ∧ (∀ r, (Ms r).complex.Acyclic) ∧ (∀ r, (Ms' r).complex.Acyclic) ∧
        ∀ I : DifferentialGradedModule.{u, v, max u v w} A,
          (IsKInjective I ∧ GradedInjective I) ↔
            ∀ (r : Idx) (f : Ms r ⟶ I), ∃ g : Ms' r ⟶ I, i r ≫ g = f := by
  classical
  have : IsGrothendieckAbelian.{max u v w}
      (SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    isGrothendieckAbelian_of_univLE.{max u v w, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  obtain ⟨T, Mt, Mt', jt, hjt, hMt, hMt', hT⟩ :=
    exists_acyclic_monomorphisms_gradedInjective_iff.{w, v, u, u, u} A
  obtain ⟨S, Msn, hMsn, hdetect⟩ :=
    exists_set_indexed_acyclic_family.{w, v, u, u, u} A
  refine ⟨T ⊕ S, Sum.elim Mt Msn, Sum.elim Mt' (fun s => cone (𝟙 (Msn s))),
    fun r => match r with
      | Sum.inl t => jt t
      | Sum.inr s => (conePackage (𝟙 (Msn s))).inclusion,
    ?_, ?_, ?_, ?_⟩
  · rintro (t | s)
    · exact hjt t
    · exact mono_cone_inclusion (𝟙 (Msn s))
  · rintro (t | s)
    · exact hMt t
    · exact (hMsn s).1
  · rintro (t | s)
    · exact hMt' t
    · exact (acyclic_cone_iff_quasiIso A (𝟙 (Msn s))).2
        (show QuasiIso (𝟙 (Msn s).complex) from inferInstance)
  · refine fun I => ⟨?_, fun hall => ?_⟩
    · rintro ⟨hK, hG⟩ (t | s) f
      · have := hjt t
        exact exists_extension_of_acyclic_of_mono hK hG (jt t) (hMt t) f
      · have := mono_cone_inclusion (𝟙 (Msn s))
        exact exists_extension_of_acyclic_of_mono hK hG
          (conePackage (𝟙 (Msn s))).inclusion (hMsn s).1 f
    · have hGI : GradedInjective I := (hT I).mpr fun t f => hall (Sum.inl t) f
      have hvan (s : S) (g : Msn s ⟶ I) : Homotopic g 0 := by
        obtain ⟨h, hh⟩ := hall (Sum.inr s) g
        have hh' : (conePackage (𝟙 (Msn s))).inclusion ≫ h = g := hh
        have hcomp : Homotopic ((conePackage (𝟙 (Msn s))).inclusion ≫ h) (0 ≫ h) :=
          (homotopic_congruence A).toIsStableUnderPostcomp.comp_right h
            (homotopic_cone_identity_inclusion (Msn s))
        rwa [hh', zero_comp] at hcomp
      refine ⟨fun N hN => ?_, hGI⟩
      have key : ∀ g : N ⟶ I, (HomotopyCategory.quotient A).map g =
          (HomotopyCategory.quotient A).map (0 : N ⟶ I) := fun g =>
        (HomotopyCategory.quotient_map_eq_iff g 0).mpr
          (homotopic_zero_of_acyclic_of_detectingFamily.{u, v, w} Msn hMsn hdetect hGI hvan
            N hN g)
      refine ⟨fun p q => ?_⟩
      obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective p
      obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient A).map_surjective q
      rw [key g, key g']

/-- Let `X` be a ringed site and let `A` be a sheaf of differential graded
algebras on it. Every right differential graded `A`-module admits a quasi-isomorphic
monomorphism into a graded injective K-injective right differential graded `A`-module,
functorially in the module. -/
@[stacks 0FT0]
theorem nonempty_gradedInjectiveKInjectiveResolution
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Nonempty (GradedInjectiveKInjectiveResolution.{u, v, w} A) := by
  obtain ⟨Idx, Ms, Ms', i, hi, hMs, hMs', hiff⟩ :=
    exists_setIndexed_acyclic_monomorphisms_iff.{u, v, w} A
  exact exists_gradedInjectiveKInjectiveResolution.{u, v, w} A Ms Ms' i hi hMs hMs'
    fun I h => (hiff I).mpr h

/-- Every right differential graded module is the source of a quasi-isomorphism into a graded
injective K-injective one. -/
theorem hasKInjectiveResolutions_dg
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    HasKInjectiveResolutions.{u, v, w} A := by
  obtain ⟨Idx, Ms, Ms', i, hi, hMs, hMs', hiff⟩ :=
    exists_setIndexed_acyclic_monomorphisms_iff.{u, v, w} A
  exact hasKInjectiveResolutions_of_detectingFamily.{u, v, w} A Ms Ms' i hi hMs hMs'
    fun I h => (hiff I).mpr h

/-! ### Products and direct sums in the derived category -/

/-- **Part (1)** of Tag 0FT9: the derived category of a sheaf of differential graded algebras on
a ringed site has arbitrary products and arbitrary direct sums. -/
theorem derivedCategory_hasProducts_and_hasCoproducts
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    HasProducts.{max u v w} (derivedCategory.{u, v, max u v w} A) ∧
      HasCoproducts.{max u v w} (derivedCategory.{u, v, max u v w} A) :=
  ⟨derivedCategory_hasProducts (hasKInjectiveResolutions_dg.{u, v, w} A),
    derivedCategory_hasCoproducts (hasKInjectiveResolutions_dg.{u, v, w} A)⟩

/-- **Part (2)** of Tag 0FT9: the image in the derived category of a direct sum of right
differential graded modules, with its canonical inclusions, is a direct sum. -/
noncomputable def isColimit_derivedCofanOfModules_dg
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {T : Type max u v w} (M : T → DifferentialGradedModule.{u, v, max u v w} A) :
    IsColimit (Cofan.mk
      ((HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (∐ M))
      (fun t => (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).map
        (Sigma.ι M t))) :=
  isColimit_derivedCofanOfModules (hasKInjectiveResolutions_dg.{u, v, w} A) M

/-- **Part (3)** of Tag 0FT9: for a family of K-injective right differential graded modules, the
image of their product in the derived category, with its canonical projections, is a product. -/
noncomputable def isLimit_derivedFanOfKInjectives_dg
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {T : Type max u v w} (I : T → DifferentialGradedModule.{u, v, max u v w} A)
    (hKI : ∀ t, IsKInjective (I t)) :
    IsLimit (Fan.mk
      ((HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (∏ᶜ I))
      (fun t => (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).map
        (Pi.π I t))) :=
  isLimit_derivedFanOfKInjectives (hasKInjectiveResolutions_dg.{u, v, w} A) I hKI

/-- **Part (3)** of Tag 0FT9, read for an arbitrary family: if `s t : M t ⟶ I t` are
quasi-isomorphisms into K-injective right differential graded modules, then the image of the
product of the `I t` in the derived category, with its canonical projections followed by the
inverses of the images of the `s t`, is a product of the images of the `M t`. -/
noncomputable def isLimit_derivedFanOfKInjectiveResolutions_dg
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {T : Type max u v w} (M I : T → DifferentialGradedModule.{u, v, max u v w} A)
    (s : ∀ t, M t ⟶ I t) (hs : ∀ t, QuasiIso (s t).toHomologicalComplex)
    (hKI : ∀ t, IsKInjective (I t)) :
    IsLimit (Fan.mk
      ((HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (∏ᶜ I))
      (fun t => (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).map
          (Pi.π I t) ≫
        (Localization.isoOfHom (toDerivedCategory.{u, v, max u v w} A)
          (quasiIsomorphisms.{u, v, max u v w} A) ((HomotopyCategory.quotient A).map (s t))
          ((quasiIsomorphisms_quotient_map_iff (s t)).2 (hs t))).inv)) := by
  let Q := HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A
  let e : ∀ t, Q.obj (M t) ≅ Q.obj (I t) := fun t =>
    Localization.isoOfHom (toDerivedCategory.{u, v, max u v w} A)
      (quasiIsomorphisms.{u, v, max u v w} A) ((HomotopyCategory.quotient A).map (s t))
      ((quasiIsomorphisms_quotient_map_iff (s t)).2 (hs t))
  have h := isLimit_derivedFanOfKInjectives_dg.{u, v, w} A I hKI
  let lift : ∀ c : Fan fun t => Q.obj (M t), c.pt ⟶ Q.obj (∏ᶜ I) := fun c =>
    h.lift (Fan.mk c.pt fun t => c.proj t ≫ (e t).hom)
  have hfac (c : Fan fun t => Q.obj (M t)) (t : T) :
      lift c ≫ Q.map (Pi.π I t) = c.proj t ≫ (e t).hom :=
    h.fac (Fan.mk c.pt fun t => c.proj t ≫ (e t).hom) ⟨t⟩
  refine Fan.IsLimit.mk _ lift (fun c t => ?_) (fun c m hm => ?_)
  · change lift c ≫ Q.map (Pi.π I t) ≫ (e t).inv = c.proj t
    rw [← Category.assoc, hfac, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · refine Fan.IsLimit.hom_ext h _ _ fun t => ?_
    change m ≫ Q.map (Pi.π I t) = lift c ≫ Q.map (Pi.π I t)
    rw [hfac, ← hm t]
    change m ≫ Q.map (Pi.π I t) = (m ≫ Q.map (Pi.π I t) ≫ (e t).inv) ≫ (e t).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Conditions

/-! ### Tag 0FT9 over a ringed site, with no side condition -/

section RingedSite

/-- Abelian groups in a universe containing the site admit sheafification, by transport from a
small model of the site. -/
theorem ringedSite_hasSheafify_addCommGrpCat (X : AlgebraicGeometry.RingedSite.{u, u, u})
    [UnivLE.{u, m}] : HasSheafify X.J AddCommGrpCat.{m} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{m, u, u} X.J

/-- In a universe containing the site, abelian-group sheafification inverts exactly the locally
bijective maps, by transport from a small model of the site. -/
theorem ringedSite_wEqualsLocallyBijective_addCommGrpCat
    (X : AlgebraicGeometry.RingedSite.{u, u, u}) [UnivLE.{u, m}] :
    X.J.WEqualsLocallyBijective AddCommGrpCat.{m} := by
  have : ((equivSmallModel.{m} X.C).inverse.inducedTopology X.J).WEqualsLocallyBijective
      AddCommGrpCat.{m} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, _, u, _, m} X.J

attribute [local instance] ringedSite_hasSheafify_addCommGrpCat
  ringedSite_wEqualsLocallyBijective_addCommGrpCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}

/-- Let `(C, O)` be a ringed site and let `(A, d)` be a sheaf of differential graded algebras on
`(C, O)`. Then (1) `D(A, d)` has both direct sums and products, (2) direct sums are obtained by
taking direct sums of differential graded `A`-modules, (3) products are obtained by taking
products of K-injective differential graded modules. The four conjuncts are the three parts, in
order, the third read in two ways:

1. the derived category has arbitrary products and arbitrary direct sums;
2. for every family `M` of right differential graded `A`-modules, the image of the direct sum
   `∐ M`, with the images of its canonical inclusions, is a direct sum in `D(A, d)`;
3. for every family `I` of K-injective right differential graded `A`-modules, the image of the
   product `∏ᶜ I`, with the images of its canonical projections, is a product in `D(A, d)`;
   and, for any family `M` with quasi-isomorphisms `s t : M t ⟶ I t` into K-injective modules,
   the image of `∏ᶜ I`, with its projections followed by the inverses of the images of the
   `s t`, is a product of the images of the `M t` in `D(A, d)`.

The modules, and the index sets of the families, lie in any universe `max u v w` containing the
site and the algebra. -/
@[stacks 0FT9]
theorem derivedCategory_sumsAndProducts
    (A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (HasProducts.{max u v w} (derivedCategory.{u, v, max u v w} A) ∧
        HasCoproducts.{max u v w} (derivedCategory.{u, v, max u v w} A)) ∧
      (∀ (T : Type max u v w) (M : T → DifferentialGradedModule.{u, v, max u v w} A),
        Nonempty (IsColimit (Cofan.mk
          ((HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (∐ M))
          (fun t => (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).map
            (Sigma.ι M t))))) ∧
      (∀ (T : Type max u v w) (I : T → DifferentialGradedModule.{u, v, max u v w} A),
        (∀ t, IsKInjective (I t)) →
          Nonempty (IsLimit (Fan.mk
            ((HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (∏ᶜ I))
            (fun t => (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).map
              (Pi.π I t))))) ∧
      (∀ (T : Type max u v w) (M I : T → DifferentialGradedModule.{u, v, max u v w} A)
        (s : ∀ t, M t ⟶ I t) (qis : ∀ t, QuasiIso (s t).toHomologicalComplex),
        (∀ t, IsKInjective (I t)) →
          Nonempty (IsLimit (Fan.mk
            ((HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).obj (∏ᶜ I))
            (fun t => (HomotopyCategory.quotient A ⋙ toDerivedCategory.{u, v, max u v w} A).map
                (Pi.π I t) ≫
              (Localization.isoOfHom (toDerivedCategory.{u, v, max u v w} A)
                (quasiIsomorphisms.{u, v, max u v w} A)
                ((HomotopyCategory.quotient A).map (s t))
                ((quasiIsomorphisms_quotient_map_iff (s t)).2 (qis t))).inv)))) :=
  ⟨derivedCategory_hasProducts_and_hasCoproducts.{u, v, w} A,
    fun _ M => ⟨isColimit_derivedCofanOfModules_dg.{u, v, w} A M⟩,
    fun _ I hKI => ⟨isLimit_derivedFanOfKInjectives_dg.{u, v, w} A I hKI⟩,
    fun _ M I s hs hKI =>
      ⟨isLimit_derivedFanOfKInjectiveResolutions_dg.{u, v, w} A M I s hs hKI⟩⟩

end RingedSite

end SheafOfModules.DifferentialGradedModule

end
