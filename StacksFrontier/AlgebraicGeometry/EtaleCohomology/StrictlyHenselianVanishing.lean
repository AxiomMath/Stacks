module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SiteAxioms
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.Etale.ResidueFieldExtension
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# Étale cohomology over a strictly henselian local ring

Let `R` be a strictly henselian local ring and let `s` be a geometric point of `Spec R`
lying over the closed point. Every object of the small étale site of `Spec R` equipped with
a lift of `s` receives a *unique* morphism from the final object `Spec R / Spec R`: a lift of
`s` to an étale `Spec R`-scheme extends to a section of its structure morphism, because `R` is
henselian with separably closed residue field, and that section is unique because the diagonal
of an étale morphism is an open immersion and `Spec R` is local.

So the category of étale neighbourhoods of `s` has an initial object, and the stalk at `s` —
a colimit over that category — is computed by the final neighbourhood alone. Hence global
sections agree with the stalk at `s`, which is an exact functor; equivalently the constant
sheaf on `ULift ℤ` is projective in the category of abelian sheaves, so all positive-degree
étale cohomology over `Spec R` vanishes.

## Main definitions

* `Stacks.StrictlyHenselian.finalNeighborhood` — the final object of the small étale site,
  viewed as an étale neighbourhood of `s`.
* `Stacks.StrictlyHenselian.globalSectionsToEtaleStalk` — the canonical map from global
  sections to the stalk at `s`.

## Main results

* `Stacks.StrictlyHenselian.isIso_globalSectionsToEtaleStalk` — global sections are the stalk
  at a geometric point over the closed point, for sheaves of sets.
* `Stacks.StrictlyHenselian.globalSections_preservesFiniteColimits` — global sections of
  abelian étale sheaves are exact.
* `Stacks.StrictlyHenselian.subsingleton_etaleCohomology` — positive-degree étale cohomology
  vanishes.

## Implementation notes

The small étale site is the size-bounded site `AlgebraicGeometry.SmallEtale` of Stacks 021B,
formed inside a chosen big étale site, and the stalk is `AlgebraicGeometry.etaleStalk` of
Stacks 040R. The canonical map is restriction from global sections to the final object,
followed by the colimit inclusion of that neighbourhood. Exactness is obtained by exhibiting
global sections as the fibre functor of a point of the site, which is where the initiality of
the final neighbourhood is used; vanishing then follows from projectivity of the constant
sheaf, since `Sheaf.H` is an `Ext` out of it.

No tag attribute is placed here, although the three results above are the whole covering set
of Tag 03QO: attribute placement on this branch is the lead's call.

## References

* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w v

namespace Stacks.StrictlyHenselian

private theorem projective_ulift_int :
    Projective (AddCommGrpCat.of (ULift.{v, 0} ℤ)) := by
  constructor
  intro E X f e he
  have hsurj : Function.Surjective e.hom :=
    (AddCommGrpCat.epi_iff_surjective e).mp he
  obtain ⟨y, hy⟩ := hsurj (f.hom (ULift.up 1))
  refine ⟨AddCommGrpCat.ofHom (uliftZMultiplesHom E y), ?_⟩
  apply AddCommGrpCat.hom_ext
  ext z
  show e.hom ((uliftZMultiplesHom E y) z) = f.hom z
  rw [uliftZMultiplesHom_apply_apply]
  have hz : z = z.down • (ULift.up (1 : ℤ)) := ULift.ext _ _ (by simp)
  calc
    e.hom (z.down • y) = z.down • e.hom y := map_zsmul _ _ _
    _ = z.down • f.hom (ULift.up 1) := by rw [hy]
    _ = f.hom (z.down • ULift.up 1) := (map_zsmul _ _ _).symm
    _ = f.hom z := (congrArg f.hom hz).symm

private theorem exists_residue_compatible_retraction
    {R A : Type u} {Ω : Type w} [CommRing R] [CommRing A] [Field Ω] [Algebra R A]
    [HenselianLocalRing R] [Algebra.Etale R A]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (α : A →+* Ω) (β : R →+* Ω) (hα : α.comp (algebraMap R A) = β)
    (hβ : RingHom.ker β = IsLocalRing.maximalIdeal R) :
    ∃ σ : A →ₐ[R] R, ∀ a, a - algebraMap R A (σ a) ∈ RingHom.ker α := by
  let P : Ideal A := RingHom.ker α
  let : P.IsPrime := RingHom.ker_isPrime α
  have hlo : P.comap (algebraMap R A) = IsLocalRing.maximalIdeal R := by
    show RingHom.ker (α.comp (algebraMap R A)) = _
    rw [hα, hβ]
  let hP : P.LiesOver (IsLocalRing.maximalIdeal R) := ⟨hlo.symm⟩
  let := hP
  have hres : Function.Bijective
      ⇑(Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P (Algebra.ofId R A)
        Ideal.LiesOver.over) := by
    let : Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal R)) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver _ _
    let : Localization.AtPrime.IsLiesOverAlgebra (IsLocalRing.maximalIdeal R) P := inferInstance
    have hfin := Algebra.IsEtaleAt.map_eq_maximalIdeal_and_finite_isSeparable_residueField
      (IsLocalRing.maximalIdeal R) P
    let : Algebra.IsSeparable (IsLocalRing.maximalIdeal R).ResidueField P.ResidueField :=
      hfin.2.2
    let e : (IsLocalRing.ResidueField R) ≃+*
        (IsLocalRing.maximalIdeal R).ResidueField :=
      RingEquiv.ofBijective (algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
        (IsLocalRing.maximalIdeal R).ResidueField)
        (IsLocalRing.maximalIdeal R).bijective_algebraMap_quotient_residueField
    let : IsSepClosed (IsLocalRing.maximalIdeal R).ResidueField := IsSepClosed.of_ringEquiv e.symm
    show Function.Bijective
      (algebraMap (IsLocalRing.maximalIdeal R).ResidueField P.ResidueField)
    exact IsSepClosed.algebraMap_bijective _ _
  exact henselian_etale_residue_point_section R A P hres

private theorem etale_section_unique
    {R : Type u} [CommRing R] [IsLocalRing R]
    (s : GeometricPoint (Spec (.of R)))
    (hs : s.LiesOver (IsLocalRing.closedPoint R))
    (T : Scheme.{u}) (g : T ⟶ Spec (.of R)) [Etale g]
    (t₁ t₂ : Spec (.of R) ⟶ T)
    (h₁ : t₁ ≫ g = 𝟙 _) (h₂ : t₂ ≫ g = 𝟙 _)
    (hp : s.hom ≫ t₁ = s.hom ≫ t₂) : t₁ = t₂ := by
  let d := pullback.diagonal g
  have : IsOpenImmersion d := inferInstance
  let w := pullback.lift t₁ t₂ (by rw [h₁, h₂])
  have hsp : s.hom ≫ w = s.hom ≫ t₁ ≫ d := by
    apply pullback.hom_ext
    · calc
        s.hom ≫ (w ≫ pullback.fst g g) = s.hom ≫ t₁ := by
          dsimp only [w]; rw [pullback.lift_fst]
        _ = s.hom ≫ t₁ ≫ d ≫ pullback.fst g g := by simp [d]
    · calc
        s.hom ≫ (w ≫ pullback.snd g g) = s.hom ≫ t₂ := by
          dsimp only [w]; rw [pullback.lift_snd]
        _ = s.hom ≫ t₁ := hp.symm
        _ = s.hom ≫ t₁ ≫ d ≫ pullback.snd g g := by simp [d]
  have hclosed : IsLocalRing.closedPoint R ∈ w ⁻¹ᵁ d.opensRange := by
    show w (IsLocalRing.closedPoint R) ∈ d.opensRange
    rw [Scheme.Hom.mem_opensRange]
    refine ⟨t₁ (IsLocalRing.closedPoint R), ?_⟩
    have heq := congrArg (fun f : s.source ⟶ pullback g g => f default) hsp
    change w (s.hom default) = d (t₁ (s.hom default)) at heq
    rw [hs] at heq
    exact heq.symm
  have htop : w ⁻¹ᵁ d.opensRange = ⊤ := IsLocalRing.closed_point_mem_iff.mp hclosed
  have hrange : Set.range w ⊆ Set.range d := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ w ⁻¹ᵁ d.opensRange := by rw [htop]; trivial
    exact (Scheme.Hom.mem_opensRange).mp hx
  let l := IsOpenImmersion.lift d w hrange
  have hl : l ≫ d = w := IsOpenImmersion.lift_fac d w hrange
  have key (p : pullback g g ⟶ T) (t : Spec (.of R) ⟶ T) (hd : d ≫ p = 𝟙 T)
      (hw : w ≫ p = t) : l = t :=
    calc
      l = l ≫ d ≫ p := by rw [hd, Category.comp_id]
      _ = w ≫ p := by rw [← Category.assoc, hl]
      _ = t := hw
  exact (key _ t₁ (by simp [d]) (pullback.lift_fst _ _ _)).symm.trans
    (key _ t₂ (by simp [d]) (pullback.lift_snd _ _ _))

private theorem exists_etale_section
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (s : GeometricPoint (Spec (.of R)))
    (hs : s.LiesOver (IsLocalRing.closedPoint R))
    (T : Scheme.{u}) (g : T ⟶ Spec (.of R)) [Etale g]
    (x : s.source ⟶ T) (hx : x ≫ g = s.hom) :
    ∃ t : Spec (.of R) ⟶ T, t ≫ g = 𝟙 _ ∧ s.hom ≫ t = x := by
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective s.hom
  let β : R →+* s.residueField := β₀.hom
  have hβ : Spec.map β₀ = s.hom := hβ₀
  have hβker : RingHom.ker β = IsLocalRing.maximalIdeal R := by
    have hp : Spec.map β₀ (default : Spec (.of s.residueField)) = IsLocalRing.closedPoint R :=
      hβ ▸ hs
    rw [RingHom.ker_eq_comap_bot]
    show (Spec.map β₀ (default : Spec (.of s.residueField))).asIdeal = _
    simpa [IsLocalRing.closedPoint] using congrArg PrimeSpectrum.asIdeal hp
  obtain ⟨A, j, hj, hxj, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (x := x default) (U := ⊤) (by simp)
  have hrange : Set.range ⇑x ⊆ Set.range ⇑j := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hxj
    refine ⟨b, ?_⟩
    simpa only [Subsingleton.elim a default] using hb
  let z : s.source ⟶ Spec A := IsOpenImmersion.lift j x hrange
  have hz : z ≫ j = x := IsOpenImmersion.lift_fac j x hrange
  have hchartEtale : Etale (j ≫ g) := by infer_instance
  obtain ⟨q, hq⟩ := Spec.map_surjective (j ≫ g)
  let : Algebra R A := q.hom.toAlgebra
  have hqEtale : RingHom.Etale q.hom :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp (by rwa [hq])
  let : Algebra.Etale R A := hqEtale.toAlgebra
  obtain ⟨α₀, hα₀⟩ := Spec.map_surjective z
  let α : A →+* s.residueField := α₀.hom
  have hα : Spec.map α₀ = z := hα₀
  have hcomp : Spec.map α₀ ≫ Spec.map q = Spec.map β₀ := by
    calc
      Spec.map α₀ ≫ Spec.map q = z ≫ Spec.map q := by rw [hα]
      _ = z ≫ (j ≫ g) := by rw [← hq]
      _ = (z ≫ j) ≫ g := by simp [Category.assoc]
      _ = x ≫ g := by rw [hz]
      _ = s.hom := hx
      _ = Spec.map β₀ := hβ.symm
  have hαβ : α.comp (algebraMap R A) = β := by
    have hhom : q ≫ α₀ = β₀ := Spec.map_inj.mp (by rw [Spec.map_comp]; exact hcomp)
    have hhom' : α.comp q.hom = β := congrArg CommRingCat.Hom.hom hhom
    simpa only [α, β, RingHom.algebraMap_toAlgebra] using hhom'
  obtain ⟨σ, hσ⟩ := exists_residue_compatible_retraction α β hαβ hβker
  have hσbase : CommRingCat.ofHom (σ.toRingHom.comp q.hom) = 𝟙 (CommRingCat.of R) := by
    apply CommRingCat.hom_ext
    ext r
    show σ (algebraMap R A r) = r
    simp
  have hαsection : α = β.comp σ.toRingHom := by
    ext a
    have hrel : α (a - algebraMap R A (σ a)) = 0 := RingHom.mem_ker.mp (hσ a)
    have hαalg : α (algebraMap R A (σ a)) = β (σ a) := by
      simpa only [RingHom.comp_apply] using congrArg (fun f : R →+* s.residueField => f (σ a)) hαβ
    have heq : α a = β (σ a) := by
      rw [map_sub, hαalg] at hrel
      exact sub_eq_zero.mp hrel
    exact heq
  let t₀ : Spec (.of R) ⟶ Spec A := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have hpoint : s.hom ≫ t₀ = z := by
    calc
      s.hom ≫ t₀ = Spec.map β₀ ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by rw [hβ]
      _ = Spec.map (CommRingCat.ofHom (β.comp σ.toRingHom)) := by
        rw [← Spec.map_comp]
        congr 1
      _ = Spec.map α₀ := by
        congr 1
        exact congrArg CommRingCat.ofHom hαsection.symm
      _ = z := hα
  have hbase : (t₀ ≫ j) ≫ g = 𝟙 (Spec (.of R)) := by
    calc
      (t₀ ≫ j) ≫ g = t₀ ≫ (j ≫ g) := by simp [Category.assoc]
      _ = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map q := by rw [hq]
      _ = Spec.map (CommRingCat.ofHom (σ.toRingHom.comp q.hom)) := by
        rw [← Spec.map_comp]
        congr 1
      _ = 𝟙 _ := by rw [hσbase]; simp
  refine ⟨t₀ ≫ j, hbase, ?_⟩
  calc
    s.hom ≫ (t₀ ≫ j) = (s.hom ≫ t₀) ≫ j := by simp [Category.assoc]
    _ = z ≫ j := by rw [hpoint]
    _ = x := hz

variable (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
  (hS : B.Contains (Spec (.of R)))
  (s : GeometricPoint (Spec (.of R)))

/-- The final object of the small étale site, equipped with the chosen lift of
the geometric point, is an étale neighborhood. -/
public def finalNeighborhood :
    (geometricPointFiber B (Spec (.of R)) hS s).Elements :=
  ⟨SmallEtale.final B (Spec (.of R)) hS,
    ⟨s.hom, by simp [SmallEtale.final]⟩⟩

/-- The canonical map from global sections to the stalk at a geometric point. -/
public def globalSectionsToEtaleStalk
    [HasWeakSheafify (SmallEtale.topology B (Spec (.of R)) hS)
      (Type (u + 1))]
    (F : Sheaf (SmallEtale.topology B (Spec (.of R)) hS)
      (Type (u + 1))) :
    (Sheaf.Γ (SmallEtale.topology B (Spec (.of R)) hS)
      (Type (u + 1))).obj F ⟶
      etaleStalk B (Spec (.of R)) hS s F.obj :=
  (Sheaf.ΓNatIsoSheafSections
      (SmallEtale.topology B (Spec (.of R)) hS)
      (Type (u + 1))
      (SmallEtale.finalIsTerminal B (Spec (.of R)) hS)).hom.app F ≫
    colimit.ι
      ((CategoryOfElements.π
        (geometricPointFiber B (Spec (.of R)) hS s)).op ⋙ F.obj)
      (op (finalNeighborhood B R hS s))

private noncomputable def finalToNeighborhood
    (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
    (hS : B.Contains (Spec (.of R))) (s : GeometricPoint (Spec (.of R)))
    [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R))
    (U : (geometricPointFiber B (Spec (.of R)) hS s).Elements) :
    finalNeighborhood B R hS s ⟶ U := by
  let T := (SmallEtale.toScheme B (Spec (.of R)) hS).obj U.1
  let g : T ⟶ Spec (.of R) := B.inclusion.map U.1.obj.hom
  letI : Etale g := U.1.property
  let hex := exists_etale_section s hs T g U.2.1 U.2.2
  let t := Classical.choose hex
  have htbase := (Classical.choose_spec hex).1
  have htpoint := (Classical.choose_spec hex).2
  let fB : B.obj (Spec (.of R)) hS ⟶ U.1.obj.left :=
    B.inclusion.preimage (show B.inclusion.obj (B.obj (Spec (.of R)) hS) ⟶
      B.inclusion.obj U.1.obj.left from t)
  have hfB : B.inclusion.map fB = t := B.inclusion.map_preimage _
  have hover : fB ≫ U.1.obj.hom = 𝟙 (B.obj (Spec (.of R)) hS) := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hfB]
    exact htbase
  let fOver : (SmallEtale.inclusion B (Spec (.of R)) hS).obj
      (SmallEtale.final B (Spec (.of R)) hS) ⟶
      (SmallEtale.inclusion B (Spec (.of R)) hS).obj U.1 :=
    Over.homMk fB hover
  let f : (SmallEtale.final B (Spec (.of R)) hS) ⟶ U.1 :=
    (SmallEtale.inclusion B (Spec (.of R)) hS).preimage fOver
  have hmap : (SmallEtale.inclusion B (Spec (.of R)) hS).map f = fOver :=
    (SmallEtale.inclusion B (Spec (.of R)) hS).map_preimage fOver
  have hf : (SmallEtale.toScheme B (Spec (.of R)) hS).map f = t := by
    change B.inclusion.map
      ((Over.forget (B.obj (Spec (.of R)) hS)).map
        ((SmallEtale.inclusion B (Spec (.of R)) hS).map f)) = t
    rw [hmap]
    exact hfB
  refine CategoryOfElements.homMk (finalNeighborhood B R hS s) U f ?_
  apply Subtype.ext
  change s.hom ≫ (SmallEtale.toScheme B (Spec (.of R)) hS).map f = U.2.1
  rw [hf]
  exact htpoint

/-- A morphism of the small étale site is a morphism of schemes over the structure maps. -/
private theorem toScheme_map_comp_structure {X Y : SmallEtale B (Spec (.of R)) hS} (f : X ⟶ Y) :
    (SmallEtale.toScheme B (Spec (.of R)) hS).map f ≫ B.inclusion.map Y.obj.hom =
      B.inclusion.map X.obj.hom := by
  change B.inclusion.map ((SmallEtale.inclusion B (Spec (.of R)) hS).map f).left ≫
    B.inclusion.map Y.obj.hom = _
  rw [← Functor.map_comp]
  exact congrArg B.inclusion.map (Over.w ((SmallEtale.inclusion B (Spec (.of R)) hS).map f))

private noncomputable def finalNeighborhood_initial
    (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
    (hS : B.Contains (Spec (.of R))) (s : GeometricPoint (Spec (.of R)))
    [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R)) :
    IsInitial (finalNeighborhood B R hS s) := by
  refine IsInitial.ofUniqueHom (fun U => finalToNeighborhood B R hS s hs U) ?_
  intro U m
  let T := (SmallEtale.toScheme B (Spec (.of R)) hS).obj U.1
  let g : T ⟶ Spec (.of R) := B.inclusion.map U.1.obj.hom
  let : Etale g := U.1.property
  let f := finalToNeighborhood B R hS s hs U
  have hbase (k : finalNeighborhood B R hS s ⟶ U) :
      (SmallEtale.toScheme B (Spec (.of R)) hS).map k.val ≫ g = 𝟙 (Spec (.of R)) := by
    rw [toScheme_map_comp_structure]
    simp [finalNeighborhood, SmallEtale.final]
  have hmPoint : s.hom ≫
      (SmallEtale.toScheme B (Spec (.of R)) hS).map m.val = U.2.1 :=
    congrArg Subtype.val m.property
  have hfPoint : s.hom ≫
      (SmallEtale.toScheme B (Spec (.of R)) hS).map f.val = U.2.1 :=
    congrArg Subtype.val f.property
  have heq := etale_section_unique s hs T g
    ((SmallEtale.toScheme B (Spec (.of R)) hS).map m.val)
    ((SmallEtale.toScheme B (Spec (.of R)) hS).map f.val)
    (hbase m) (hbase f) (by rw [hmPoint, hfPoint])
  apply CategoryOfElements.ext
  exact (SmallEtale.toScheme B (Spec (.of R)) hS).map_injective heq

/-- The final object of the small étale site, with its canonical lift of the geometric point,
is initial among the étale neighbourhoods of that point: the lift extends to a section of the
structure morphism of any neighbourhood, uniquely. -/
public theorem nonempty_isInitial_finalNeighborhood
    (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
    (hS : B.Contains (Spec (.of R))) (s : GeometricPoint (Spec (.of R)))
    [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R)) :
    Nonempty (IsInitial (finalNeighborhood B R hS s)) :=
  ⟨finalNeighborhood_initial B R hS s hs⟩

private noncomputable def smallEtalePoint
    (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
    (hS : B.Contains (Spec (.of R))) (s : GeometricPoint (Spec (.of R)))
    [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R)) :
    (SmallEtale.topology B (Spec (.of R)) hS).Point where
  fiber := geometricPointFiber B (Spec (.of R)) hS s
  isCofiltered := by
    let I := finalNeighborhood B R hS s
    have hI := finalNeighborhood_initial B R hS s hs
    let : IsCofilteredOrEmpty
        (geometricPointFiber B (Spec (.of R)) hS s).Elements := {
      cone_objs := fun X Y => ⟨I, hI.to X, hI.to Y, trivial⟩
      cone_maps := by
        intro X Y f g
        exact ⟨I, hI.to X, hI.hom_ext _ _⟩
    }
    let : Nonempty (geometricPointFiber B (Spec (.of R)) hS s).Elements := ⟨I⟩
    exact IsCofiltered.mk
  initiallySmall := inferInstance
  jointly_surjective := by
    intro X S hmem x
    induction hmem with
    | of X P hR =>
        obtain ⟨E, hEq, hCover⟩ := hR
        let iSmall := SmallEtale.inclusion B (Spec (.of R)) hS
        let iOver := BigEtaleOver.forget B (Spec (.of R)) hS
        let toSch := (iSmall ⋙ iOver) ⋙ schemeBelowInclusion B.cutoff
        let fS := fun i : E.I₀ => toSch.map (E.f i)
        have hB : B.IsCovering ⟨(iSmall ⋙ iOver).obj X,
            E.map (iSmall ⋙ iOver)⟩ := hCover
        have hFam : Presieve.ofArrows (fun i => toSch.obj (E.X i)) fS ∈
            Scheme.etalePrecoverage (toSch.obj X) := by
          have hEtale := BigEtaleSite.IsCovering.etale hB
          simpa [IsEtaleCovering, Scheme.etalePrecoverage,
            PreZeroHypercover.presieve₀, PreZeroHypercover.map,
            SmallEtale.toScheme, BigEtaleOver.toScheme,
            BigEtaleOver.forget, SmallEtale.inclusion,
            schemeBelowInclusion, Functor.comp_obj, Functor.comp_map,
            iSmall, iOver, toSch, fS] using hEtale
        have hCoverPoint := (Scheme.ofArrows_mem_precoverage_iff (@Etale)).mp hFam
        obtain ⟨i, ⟨y, hy⟩⟩ := hCoverPoint.1 (x.1 default)
        have : Etale (fS i) := hCoverPoint.2 i
        obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
          (fS i) x.1 y hy
        refine ⟨E.X i, E.f i, ?_, ⟨l, ?_⟩, ?_⟩
        · rw [hEq, Sieve.generate_apply]
          exact ⟨E.X i, 𝟙 _, E.f i, E.presieve₀_f i, by simp⟩
        · calc
            l ≫ B.inclusion.map (E.X i).obj.hom =
                l ≫ fS i ≫ B.inclusion.map X.obj.hom :=
                (congrArg (l ≫ ·) (toScheme_map_comp_structure B R hS (E.f i))).symm
            _ = x.1 ≫ B.inclusion.map X.obj.hom := by rw [← Category.assoc, hl]
            _ = s.hom := x.2
        · exact Subtype.ext hl
    | top X =>
        exact ⟨X, 𝟙 X, by simp, x, by simp⟩
    | pullback X S hCover Y f h =>
        obtain ⟨Z, g, hmem, z, hz⟩ := h ((geometricPointFiber B
          (Spec (.of R)) hS s).map f x)
        let Q := pullback f g
        let pY : Q ⟶ Y := pullback.fst f g
        let pZ : Q ⟶ Z := pullback.snd f g
        have hcompat : z.1 ≫ (SmallEtale.toScheme B
            (Spec (.of R)) hS).map g =
            x.1 ≫ (SmallEtale.toScheme B (Spec (.of R)) hS).map f :=
          congrArg Subtype.val hz
        let c : PullbackCone
            ((SmallEtale.toScheme B (Spec (.of R)) hS).map f)
            ((SmallEtale.toScheme B (Spec (.of R)) hS).map g) :=
          PullbackCone.mk x.1 z.1 hcompat.symm
        let hlim : IsLimit ((pullback.cone f g).map
            (SmallEtale.toScheme B (Spec (.of R)) hS)) :=
          ((pullback.cone f g).isLimitMapConeEquiv
            (SmallEtale.toScheme B (Spec (.of R)) hS)).1
            (isLimitOfPreserves (SmallEtale.toScheme B
              (Spec (.of R)) hS) (pullback.isLimit f g))
        let q : s.source ⟶ (SmallEtale.toScheme B
            (Spec (.of R)) hS).obj Q := hlim.lift c
        have hqY : q ≫ (SmallEtale.toScheme B
            (Spec (.of R)) hS).map pY = x.1 :=
          hlim.fac c WalkingCospan.left
        have hqZ : q ≫ (SmallEtale.toScheme B
            (Spec (.of R)) hS).map pZ = z.1 :=
          hlim.fac c WalkingCospan.right
        have hqbase : q ≫ B.inclusion.map Q.obj.hom = s.hom := by
          calc
            q ≫ B.inclusion.map Q.obj.hom =
                q ≫ (SmallEtale.toScheme B (Spec (.of R)) hS).map pY ≫
                  B.inclusion.map Y.obj.hom := by rw [toScheme_map_comp_structure]
            _ = x.1 ≫ B.inclusion.map Y.obj.hom := by rw [← Category.assoc, hqY]
            _ = s.hom := x.2
        let qx : (geometricPointFiber B
            (Spec (.of R)) hS s).obj Q := ⟨q, hqbase⟩
        have hqpoint : ((geometricPointFiber B
            (Spec (.of R)) hS s).map pY) qx = x :=
          Subtype.ext hqY
        refine ⟨Q, pY, ?_, qx, hqpoint⟩
        rw [Sieve.pullback_apply, pullback.condition]
        exact S.downward_closed hmem pZ
    | transitive X S T hCover hT hleS hleT =>
        obtain ⟨Y, f, hSf, y, hy⟩ := hleS x
        obtain ⟨Z, g, hTf, z, hz⟩ := hleT hSf y
        refine ⟨Z, g ≫ f, ?_, z, ?_⟩
        · rw [Sieve.pullback_apply] at hTf
          simpa [Category.assoc] using hTf
        · change ((geometricPointFiber B
            (Spec (.of R)) hS s).map f)
            (((geometricPointFiber B
              (Spec (.of R)) hS s).map g) z) = x
          rw [hz, hy]

private noncomputable def closedGeometricPoint
    (R : Type u) [CommRing R] [IsLocalRing R] :
    GeometricPoint (Spec (.of R)) :=
  ⟨AlgebraicClosure (IsLocalRing.ResidueField R),
    Spec.map (CommRingCat.ofHom
      ((algebraMap (IsLocalRing.ResidueField R)
          (AlgebraicClosure (IsLocalRing.ResidueField R))).comp
        (IsLocalRing.residue R)))⟩

private theorem closedGeometricPoint_liesOver
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (closedGeometricPoint R).LiesOver (IsLocalRing.closedPoint R) := by
  dsimp only [GeometricPoint.LiesOver, closedGeometricPoint]
  let K := IsLocalRing.ResidueField R
  let Ω := AlgebraicClosure K
  let f : R →+* Ω := (algebraMap K Ω).comp (IsLocalRing.residue R)
  have hf : RingHom.ker f = IsLocalRing.maximalIdeal R := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap K Ω).injective]
    exact IsLocalRing.ker_residue
  show (Spec.map (CommRingCat.ofHom f)) _ = IsLocalRing.closedPoint R
  apply PrimeSpectrum.ext
  rw [Spec.map_apply]
  show Ideal.comap f _ = _
  have hbot : (default : Spec (.of Ω)).asIdeal = ⊥ :=
    @Ideal.eq_bot_of_prime Ω _ _ (default : Spec (.of Ω)).isPrime
  rw [hbot]
  exact hf

private noncomputable def closedPointEtalePoint
    (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
    (hS : B.Contains (Spec (.of R)))
    (s : GeometricPoint (Spec (.of R)))
    [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R)) :
    CategoryTheory.GrothendieckTopology.Point.{u}
      (SmallEtale.topology B (Spec (.of R)) hS) :=
  smallEtalePoint B R hS s hs

/-- On a strictly henselian local ring, restriction to the final object followed by the colimit
inclusion at the final neighbourhood is an isomorphism. -/
private theorem isIso_sections_final_comp_colimit_ι
    [StrictlyHenselianLocalRing R] (hs : s.LiesOver (IsLocalRing.closedPoint R))
    {C : Type*} [Category C] [HasWeakSheafify (SmallEtale.topology B (Spec (.of R)) hS) C]
    (F : Sheaf (SmallEtale.topology B (Spec (.of R)) hS) C)
    [HasColimit ((CategoryOfElements.π (geometricPointFiber B (Spec (.of R)) hS s)).op ⋙ F.obj)] :
    IsIso ((Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B (Spec (.of R)) hS) C
        (SmallEtale.finalIsTerminal B (Spec (.of R)) hS)).hom.app F ≫
      colimit.ι ((CategoryOfElements.π (geometricPointFiber B (Spec (.of R)) hS s)).op ⋙ F.obj)
        (op (finalNeighborhood B R hS s))) := by
  have hΓ : IsIso ((Sheaf.ΓNatIsoSheafSections (SmallEtale.topology B (Spec (.of R)) hS) C
      (SmallEtale.finalIsTerminal B (Spec (.of R)) hS)).hom.app F) := inferInstance
  have hι : IsIso (colimit.ι ((CategoryOfElements.π
      (geometricPointFiber B (Spec (.of R)) hS s)).op ⋙ F.obj) (op (finalNeighborhood B R hS s))) :=
    (colimit.isColimit _).isIso_ι_app_of_isTerminal _
      (IsInitial.op _ (finalNeighborhood_initial B R hS s hs))
  exact Iso.isIso_hom ((@asIso _ _ _ _ _ hΓ) ≪≫ (@asIso _ _ _ _ _ hι))

/-- For a strictly henselian local ring, the canonical global-sections-to-stalk
map is an isomorphism for every sheaf of sets. -/
@[stacks 03QO "global sections equal the closed geometric stalk",
  sga "4 VIII 8.6" "strictly henselian, n=0"]
public theorem isIso_globalSectionsToEtaleStalk
    [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R))
    [HasWeakSheafify (SmallEtale.topology B (Spec (.of R)) hS)
      (Type (u + 1))]
    (F : Sheaf (SmallEtale.topology B (Spec (.of R)) hS)
      (Type (u + 1))) :
    IsIso (globalSectionsToEtaleStalk B R hS s F) := by
  exact isIso_sections_final_comp_colimit_ι B R hS s hs F

private noncomputable def globalSectionsToPointFiber
    (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
    (hS : B.Contains (Spec (.of R)))
    (s : GeometricPoint (Spec (.of R)))
    [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R))
    [HasSheafify (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1}] :
    Sheaf.Γ (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1} ⟶
    (closedPointEtalePoint B R hS s hs).sheafFiber.{u, u, u + 1, u + 1, u + 2}
      (A := AddCommGrpCat.{u + 1}) := by
  let J := SmallEtale.topology B (Spec (.of R)) hS
  let T := SmallEtale.final B (Spec (.of R)) hS
  let I := finalNeighborhood B R hS s
  refine {
    app F := (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{u + 1}
      (SmallEtale.finalIsTerminal B (Spec (.of R)) hS)).hom.app F ≫
      colimit.ι ((CategoryOfElements.π
        (geometricPointFiber B (Spec (.of R)) hS s)).op ⋙ F.obj)
        (op I)
    naturality := ?_ }
  intro F G f
  let γ := Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{u + 1}
    (SmallEtale.finalIsTerminal B (Spec (.of R)) hS)
  let Φ := closedPointEtalePoint B R hS s hs
  have hobj : I.1 = T := by rfl
  let x : Φ.fiber.obj T := hobj ▸ I.2
  change (Sheaf.Γ J AddCommGrpCat.{u + 1}).map f ≫ γ.hom.app G ≫
      Φ.toPresheafFiber T x G.obj =
    γ.hom.app F ≫ Φ.toPresheafFiber T x F.obj ≫ Φ.presheafFiber.map f.hom
  calc
    (Sheaf.Γ J AddCommGrpCat.{u + 1}).map f ≫ γ.hom.app G ≫
        Φ.toPresheafFiber T x G.obj =
        (γ.hom.app F ≫ ((sheafSections J AddCommGrpCat.{u + 1}).obj
          (op T)).map f ≫ Φ.toPresheafFiber T x G.obj) := by
          simp [T]
    _ = γ.hom.app F ≫ Φ.toPresheafFiber T x F.obj ≫
        Φ.presheafFiber.map f.hom := by
          simp [T, sheafSections]

private theorem isIso_globalSectionsToPointFiber_app
    (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
    (hS : B.Contains (Spec (.of R)))
    (s : GeometricPoint (Spec (.of R)))
    [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R))
    [HasSheafify (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1}]
    (F : Sheaf (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1}) :
    IsIso ((globalSectionsToPointFiber B R hS s hs).app F) := by
  exact isIso_sections_final_comp_colimit_ι B R hS s hs F

private noncomputable def globalSectionsIsoPointFiber
    (B : BigEtaleSite.{u}) (R : Type u) [CommRing R]
    (hS : B.Contains (Spec (.of R)))
    (s : GeometricPoint (Spec (.of R)))
    [StrictlyHenselianLocalRing R]
    (hs : s.LiesOver (IsLocalRing.closedPoint R))
    [HasSheafify (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1}] :
    Sheaf.Γ (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1} ≅
    (closedPointEtalePoint B R hS s hs).sheafFiber.{u, u, u + 1, u + 1, u + 2}
      (A := AddCommGrpCat.{u + 1}) :=
  NatIso.ofComponents
    (fun F => by
      letI := isIso_globalSectionsToPointFiber_app B R hS s hs F
      exact asIso ((globalSectionsToPointFiber B R hS s hs).app F))
    (by
      intro F G f
      exact (globalSectionsToPointFiber B R hS s hs).naturality f)

/-- Global sections of abelian étale sheaves on a strictly henselian local
scheme are exact. As a right adjoint, this functor already preserves limits. -/
@[stacks 03QO "exactness of global sections"]
public instance globalSections_preservesFiniteColimits
    [StrictlyHenselianLocalRing R]
    [HasSheafify (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1}] :
    PreservesFiniteColimits
      (Sheaf.Γ (SmallEtale.topology B (Spec (.of R)) hS)
        AddCommGrpCat.{u + 1}) := by
  let s := closedGeometricPoint R
  have hs : s.LiesOver (IsLocalRing.closedPoint R) := closedGeometricPoint_liesOver R
  let Φ := closedPointEtalePoint B R hS s hs
  have : PreservesFiniteColimits (Φ.sheafFiber (A := AddCommGrpCat.{u + 1})) := inferInstance
  exact preservesFiniteColimits_of_natIso
    (globalSectionsIsoPointFiber B R hS s hs).symm

/-- Positive-degree étale cohomology of an abelian sheaf over a strictly
henselian local scheme vanishes. -/
@[stacks 03QO "vanishing of positive-degree étale cohomology",
  sga "4 VIII 8.6" "strictly henselian, p≥1"]
public theorem subsingleton_etaleCohomology
    [StrictlyHenselianLocalRing R]
    [HasSheafify (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1})]
    (F : Sheaf (SmallEtale.topology B (Spec (.of R)) hS)
      AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Sheaf.H.{w, u + 1} F p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  let J := SmallEtale.topology B (Spec (.of R)) hS
  let Γ := Sheaf.Γ J AddCommGrpCat.{u + 1}
  let γ := Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{u + 1}
    (SmallEtale.finalIsTerminal B (Spec (.of R)) hS)
  let : PreservesFiniteColimits Γ := globalSections_preservesFiniteColimits B R hS
  let : Functor.PreservesEpimorphisms Γ := inferInstance
  let : Functor.PreservesEpimorphisms
      ((sheafSections J AddCommGrpCat.{u + 1}).obj
        (op (SmallEtale.final B (Spec (.of R)) hS))) :=
    Functor.PreservesEpimorphisms.of_iso γ
  let adj := constantSheafAdj J AddCommGrpCat.{u + 1}
    (SmallEtale.finalIsTerminal B (Spec (.of R)) hS)
  let : Projective ((constantSheaf J AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) :=
    adj.map_projective _ (projective_ulift_int.{u + 1})
  show Subsingleton (CategoryTheory.Abelian.Ext.{w}
    ((constantSheaf J AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift ℤ))) F (n + 1))
  exact CategoryTheory.Abelian.Ext.subsingleton_of_projective _ _ n

end Stacks.StrictlyHenselian
