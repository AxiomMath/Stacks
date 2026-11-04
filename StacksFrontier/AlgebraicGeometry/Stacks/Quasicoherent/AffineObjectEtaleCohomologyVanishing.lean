module

public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfCohomologyEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineObjectCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence

/-!
# Cohomology over an affine object of a module cartesian along étale morphisms of affines

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `ℱ` a sheaf of `𝒪_𝒳`-modules
on the associated **étale** site, with module sections in the universe `u` of the schemes.
Suppose that for every object `x` lying over an affine scheme `X` and every `z ⟶ x` lying over
an étale morphism of affine schemes `Z ⟶ X` the comparison
`Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} ℱ(x) ⟶ ℱ(z)` is bijective — as it is for a locally quasi-coherent module
(Stacks 06WJ, with Stacks 03DX on the small étale site).  Then `Hⁿ(x, ℱ) = 0` for `n > 0` at
every object `x` lying over an affine scheme.

This is the étale counterpart of
`AlgebraicGeometry.FibredSite.isZero_rightDerived_evaluation_of_isAffine`, by the same argument:
Stacks 03F9 for the finite étale coverings by objects lying over affine schemes, which are
cofinal (`AlgebraicGeometry.FibredSite.exists_affineEtaleCoverings_le`, from Stacks 0218 on the
big site), and Stacks 03FJ on them
(`AlgebraicGeometry.FibredSite.isZero_cechCohomology_succ_of_tensorToSections` with `P` étale).

## Main results

* `AlgebraicGeometry.FibredSite.isCartesianAlongEtaleAffines_of_isLocallyQuasicoherent`: a
  locally quasi-coherent module satisfies the cartesian condition.
* `AlgebraicGeometry.FibredSite.exists_affineEtaleCoverings_le`: the cofinality.
* `AlgebraicGeometry.FibredSite.isZero_sheafCohomology_of_isAffine_etale` and
  `AlgebraicGeometry.FibredSite.isZero_rightDerived_evaluation_of_isAffine_etale`: **the
  vanishing**.

## References

* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CechSite
  Stacks.Cohomology.ModuleDirectImageOnACover

universe v u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The cartesian condition along étale morphisms of affines: the comparison
`Γ(Z, 𝒪) ⊗_{Γ(X, 𝒪)} ℱ(x) ⟶ ℱ(z)` is invertible at every object `z ⟶ x` of the slice at an
object `x` lying over an affine scheme, with `z` lying over an affine scheme étale over it. -/
def IsCartesianAlongEtaleAffines
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .etale)) : Prop :=
  ∀ (x : 𝒳), IsAffine (schemeOf B S hS p x) → ∀ Z : Over x, IsAffine (schemeOf B S hS p Z.left) →
    Etale ((sliceToSchemes B S hS p x).obj Z).hom →
      IsIso (tensorToSectionsApp B S hS p hp .etale x F (op Z))

/-- **A locally quasi-coherent module is cartesian along étale morphisms of affines**: the
comparison `tensorToSectionsApp` at `z ⟶ x` is the base-change comparison of the restriction map
(`AlgebraicGeometry.FibredSite.isIso_tensorToSectionsApp_of_isIso_restrictionBaseChange`), which
is invertible for a locally quasi-coherent module
(`AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange`). -/
theorem isCartesianAlongEtaleAffines_of_isLocallyQuasicoherent (E : BigEtaleSite.{u})
    (h : E.cutoff = B.cutoff)
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .etale))
    (hF : Stack.IsLocallyQuasicoherent B E h S hS p hp F.val) :
    IsCartesianAlongEtaleAffines B S hS p hp F := fun x hx Z hZ hét =>
  isIso_tensorToSectionsApp_of_isIso_restrictionBaseChange B S hS p hp .etale x F Z
    ((Stack.isLocallyQuasicoherent_iff_forall_isIso_restrictionBaseChange B E h S hS p hp F).1
      hF Z.hom hZ hx hét)

/-- The finite étale coverings by objects lying over affine schemes, of objects lying over affine
schemes. -/
def affineEtaleCoverings (x : 𝒳) :
    Set { E : PreZeroHypercover.{u} x //
      E.sieve₀ ∈ BigFppfOver.associatedTopology B S hS p .etale x } :=
  { E | IsAffine (schemeOf B S hS p x) ∧ Finite E.1.I₀ ∧
      (∀ i, IsAffine (schemeOf B S hS p (E.1.X i))) ∧
      Presieve.ofArrows (fun i => schemeOf B S hS p (E.1.X i))
        (fun i => (p ⋙ BigFppfOver.toScheme B S hS).map (E.1.f i)) ∈
      Scheme.fppfPrecoverage (schemeOf B S hS p x) ∧
      ∀ i, Etale ((p ⋙ BigFppfOver.toScheme B S hS).map (E.1.f i)) }

include hp in
/-- **The finite étale coverings by affine objects are cofinal** among the coverings of an
object lying over an affine scheme, for the associated étale topology. -/
theorem exists_affineEtaleCoverings_le {x : 𝒳} (hx : IsAffine (schemeOf B S hS p x))
    (R : Sieve x) (hR : R ∈ BigFppfOver.associatedTopology B S hS p .etale x) :
    ∃ E : { E : PreZeroHypercover.{u} x //
        E.sieve₀ ∈ BigFppfOver.associatedTopology B S hS p .etale x },
      E ∈ affineEtaleCoverings B S hS p x ∧ E.1.sieve₀ ≤ R := by
  classical
  have hR₀ : R.functorPushforward p ∈ BigFppfOver.baseOverTopology B S hS .etale (p.obj x) :=
    (Functor.mem_inheritedTopology_iff_functorPushforward p
      (BigFppfOver.baseOverTopology B S hS .etale) hp R).mp hR
  have hR' : R.functorPushforward p ∈ (etaleTopology B).over (B.obj hS) (p.obj x) := hR₀
  obtain ⟨E, hfin, haff, hEt, hle⟩ :=
    BigFppfOver.exists_finite_affine_etaleCovering_refinement B S hS hx hR'
  have hmem : ∀ k : E.I₀, ∃ (y : 𝒳) (g : y ⟶ x) (h : E.X k ⟶ p.obj y),
      R g ∧ E.f k = h ≫ p.map g := fun k => by
    obtain ⟨y, g, h, hg, hf⟩ := hle _ _ (E.presieve₀_f k)
    exact ⟨y, g, h, hg, hf⟩
  choose y g h hg hfac using hmem
  choose z φ hφ using fun k => hp.exists_lift (h k) (y k) rfl
  have _ : ∀ k, p.IsHomLift (h k) (φ k) := hφ
  have hdom : ∀ k, p.obj (z k) = E.X k := fun k => IsHomLift.domain_eq p (h k) (φ k)
  have hmap : ∀ k, p.map (φ k ≫ g k) = eqToHom (hdom k) ≫ E.f k := by
    intro k
    rw [p.map_comp, IsHomLift.fac' p (h k) (φ k), hfac k]
    simp
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin E.I₀
  let E' : PreZeroHypercover.{u} x :=
    ⟨ULift (Fin n), fun i => z (e.symm i.down), fun i => φ (e.symm i.down) ≫ g (e.symm i.down)⟩
  let L := BigFppfOver.toScheme B S hS
  obtain ⟨hsurj, hEtk⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp hEt.2
  have hEtk' : ∀ k, Etale (L.map (E.f k)) := hEtk
  have hEtE' : ∀ i : ULift (Fin n), Etale ((p ⋙ L).map (E'.f i)) := by
    intro i
    show Etale (L.map (p.map (φ (e.symm i.down) ≫ g (e.symm i.down))))
    rw [hmap, L.map_comp]
    have := hEtk' (e.symm i.down)
    infer_instance
  have hcovE' : E'.sieve₀ ∈ BigFppfOver.associatedTopology B S hS p .etale x := by
    apply (Functor.mem_inheritedTopology_iff_functorPushforward p _ hp _).mpr
    have hEcov : Sieve.generate E.presieve₀ ∈ (etaleTopology B).over (B.obj hS) (p.obj x) := by
      rw [GrothendieckTopology.mem_over_iff]
      show Sieve.overEquiv _ (Sieve.ofArrows E.X E.f) ∈ _
      rw [Sieve.overEquiv_ofArrows]
      have hpre : (E.map (BigFppfOver.forget B S hS)).presieve₀ ∈
          etalePrecoverage B ((BigFppfOver.forget B S hS).obj (p.obj x)) := ⟨_, rfl, hEt⟩
      exact Precoverage.generate_mem_toGrothendieck hpre
    refine GrothendieckTopology.superset_covering _ ?_ hEcov
    rintro _ _ ⟨_, a, _, ⟨k⟩, rfl⟩
    have key : ∀ (j j' : E.I₀), j' = j → E'.sieve₀ (φ j' ≫ g j') →
        E'.sieve₀ (φ j ≫ g j) := by
      rintro j j' rfl h
      exact h
    have hk : E'.sieve₀ (φ k ≫ g k) :=
      key k (e.symm (e k)) (e.symm_apply_apply k) (Sieve.ofArrows_mk E'.X E'.f ⟨e k⟩)
    refine ⟨z k, φ k ≫ g k, a ≫ eqToHom (hdom k).symm, hk, ?_⟩
    rw [hmap k]
    simp
  refine ⟨⟨E', hcovE'⟩, ⟨hx, inferInstance, fun i => ?_, ?_, hEtE'⟩, ?_⟩
  · show IsAffine (L.obj (p.obj (z (e.symm i.down))))
    rw [hdom]
    exact haff _
  · have hEf : Presieve.ofArrows (fun k => L.obj (E.X k)) (fun k => L.map (E.f k)) ∈
        Scheme.fppfPrecoverage (L.obj (p.obj x)) := by
      unfold Scheme.fppfPrecoverage
      refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun t => ?_, fun k => ?_⟩
      · obtain ⟨k, hk⟩ := hsurj t
        exact ⟨k, hk⟩
      · have := hEtk' k
        exact ⟨inferInstance, inferInstance⟩
    have hEf' := Scheme.mem_fppfPrecoverage_of_equiv e.symm hEf
    have hEf'' := Scheme.mem_fppfPrecoverage_of_equiv (Equiv.ulift (α := Fin n)) hEf'
    refine Scheme.mem_fppfPrecoverage_of_forall_eq_comp
      (fun i => L.mapIso (eqToIso (hdom (e.symm i.down)))) (fun i => ?_) hEf''
    show L.map (p.map (φ (e.symm i.down) ≫ g (e.symm i.down))) = _
    rw [hmap, L.map_comp]
    rfl
  · rintro _ _ ⟨_, a, _, ⟨i⟩, rfl⟩
    rw [← Category.assoc]
    exact R.downward_closed (hg _) _

variable [HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (BigFppfOver.associatedTopology B S hS p .etale) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf (BigFppfOver.associatedTopology B S hS p .etale) AddCommGrpCat.{u})]
  [(BigFppfOver.associatedTopology B S hS p .etale).WEqualsLocallyBijective AddCommGrpCat.{u}]

include hp in
/-- **The étale cohomology of the underlying abelian sheaf of a module cartesian along étale
morphisms of affines vanishes in positive degrees over every object lying over an affine
scheme.** -/
theorem isZero_sheafCohomology_of_isAffine_etale
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .etale))
    (hF : IsCartesianAlongEtaleAffines B S hS p hp F) {x : 𝒳}
    (hx : IsAffine (schemeOf B S hS p x)) (n : ℕ) (hn : 0 < n) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf (ringStructureSheafCore B S hS p hp .etale)).obj
      F) n x) := by
  let : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  let hfl : ∀ y : 𝒳, HasFiniteLimits (Over y) :=
    fun y => hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : MorphismProperty.ContainsIdentities @Etale :=
    ⟨fun X => inferInstanceAs (Etale (𝟙 X))⟩
  let : MorphismProperty.IsStableUnderComposition @Etale :=
    ⟨fun f g hf hg => by have := hf; have := hg; exact inferInstanceAs (Etale (f ≫ g))⟩
  refine sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives.{u, u, u, v}
    (BigFppfOver.associatedTopology B S hS p .etale) {y | IsAffine (schemeOf B S hS p y)}
    (affineEtaleCoverings B S hS p) (fun E _ q i => inferInstance) ?_ ?_ _ ?_ x hx n hn
  · intro y E hE
    obtain ⟨hy, hfin, haff, hfppf, het⟩ := hE
    exact ⟨hy, haff, fun q i => (isAffine_prop_piObj B S hS p hp @Etale hy E.1 haff het q i).1⟩
  · intro y hy R hR
    exact exists_affineEtaleCoverings_le B S hS p hp hy R hR
  · intro y E hE q hq
    obtain ⟨hy, hfin, haff, hfppf, het⟩ := hE
    exact isZero_cechCohomology_succ_of_tensorToSections B S hS p hp @Etale hy E.1 hfin haff
      hfppf het _ (abelianPresheaf B S hS p hp .etale F) (tensorToSections B S hS p hp .etale y F)
      (fun Z hZ hZf => hF y hy Z hZ hZf) q hq

variable [EnoughInjectives (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .etale))]
  [HasExt.{max v u} (Sheaf (BigFppfOver.associatedTopology B S hS p .etale) AddCommGrpCat.{u})]
  [HasExt.{max v u} (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .etale))]

include hp in
/-- **The right derived functors of sections over an object lying over an affine scheme vanish
in positive degrees on a module on the associated étale site cartesian along étale morphisms of
affines.** -/
theorem isZero_rightDerived_evaluation_of_isAffine_etale
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .etale))
    (hF : IsCartesianAlongEtaleAffines B S hS p hp F) {x : 𝒳}
    (hx : IsAffine (schemeOf B S hS p x)) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafOfModules.evaluation (ringStructureSheafCore B S hS p hp .etale)
      (op x)).rightDerived n).obj F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{v, u, u}
    (BigFppfOver.associatedTopology B S hS p .etale) (ringStructureSheafCore B S hS p hp .etale)
    x m F (isZero_sheafCohomology_of_isAffine_etale B S hS p hp F hF hx (m + 1) (by omega))

end AlgebraicGeometry.FibredSite
