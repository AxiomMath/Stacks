module

public import StacksFrontier.Deformation.InfinitesimalAutomorphism.FreeTransitiveAction
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Tangent
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentVectorSpace
public import StacksFrontier.Deformation.LiftsOfObjects.InfinitesimalDifference

/-!
# Infinitesimal automorphisms over the trivial extension by the kernel

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` satisfying (RS), let `x' ⟶ x` be a
morphism lying over a surjection `A' → A` whose kernel `I` is annihilated by the maximal
ideal of `A'`, and let `x₀` be a pushforward of `x'` to the special fibre. The kernel `I` is
then a finite-dimensional vector space over the residue field, and the difference coordinate
`(a₁, a₂) ↦ (ā₁, a₂ - a₁)` presents a fibre square `A' ×_A A'` as the fibre square
`A' ×_k (k ⊕ I)` of `A'` and the trivial extension `k ⊕ I` over `k`.

The automorphisms of the (RS) fibre square of `x'` with itself over `x` that are trivial on the
first projection form a group isomorphic to the group `Inf(x₀[I]/x₀)` of infinitesimal
automorphisms, relative to `x₀`, of a pushforward `x₀[I]` of the square to `k ⊕ I`, and
`Inf(x'/x)` carries a free and transitive action by `Inf(x₀[I]/x₀)`.

## Main definitions

* `Deformation.isoOfBijectiveHom`: a morphism of `𝒞_Λ` with bijective underlying map is an
  isomorphism.

## Main results

* `Deformation.surjective_hom_residueMorphism`: the canonical map to the residue-field object
  is surjective.
* `Deformation.isPullback_infinitesimalMap`: the difference coordinate of a surjection with
  annihilated kernel presents the concrete self-fibre square `A' ×_A A'` as the fibre square
  of `A'` and the trivial extension `k ⊕ I` over the residue field.
* `Deformation.exists_isPullback_kernelTrivialExtension`: the same presentation for an
  arbitrary fibre square of `A'` with itself over `A`.
* `Deformation.exists_relativeInfinitesimalAutomorphisms_kernelTrivialExtension_mulEquiv`: the
  resulting identification of the automorphisms of the (RS) fibre square, trivial on the first
  projection, with `Inf(x₀[I]/x₀)`.
* `Deformation.exists_relativeInfinitesimalAutomorphisms_kernelTrivialExtension_action`: the
  infinitesimal automorphisms of `x'` over `x` carry a free and transitive action by
  `Inf(x₀[I]/x₀)`.

## References

* [Stacks Project, Tag 06GH](https://stacks.math.columbia.edu/tag/06GH)
* [Stacks Project, Tag 06GJ](https://stacks.math.columbia.edu/tag/06GJ)
* [Stacks Project, Tag 06IA](https://stacks.math.columbia.edu/tag/06IA)
* [Stacks Project, Tag 06J2](https://stacks.math.columbia.edu/tag/06J2)
* [Stacks Project, Tag 06J3](https://stacks.math.columbia.edu/tag/06J3)
* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
* [Stacks Project, Tag 06JP](https://stacks.math.columbia.edu/tag/06JP)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06JY](https://stacks.math.columbia.edu/tag/06JY)
-/

@[expose] public section

namespace Deformation

/-! ### Elementary facts about `𝒞_Λ` -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The canonical map to the residue-field object is the residue, read through the structural
identification of the residue field with `k`. -/
public theorem hom_residueMorphism_apply (A : ArtinianLocalAlgCat.{u, w, w} Λ k) (a : A) :
    (residueMorphism A).hom a = ULift.up (A.residueEquiv (residue A a)) := rfl

/-- The canonical map to the residue-field object is surjective. -/
public theorem surjective_hom_residueMorphism (A : ArtinianLocalAlgCat.{u, w, w} Λ k) :
    Function.Surjective (residueMorphism A).hom := by
  intro c
  obtain ⟨c⟩ := c
  obtain ⟨a, ha⟩ := residue_surjective (R := A) (A.residueEquiv.symm c)
  exact ⟨a, by rw [hom_residueMorphism_apply, ha, A.residueEquiv.apply_symm_apply]⟩

/-- A morphism of `𝒞_Λ` whose underlying algebra map is bijective is an isomorphism. -/
public noncomputable def isoOfBijectiveHom {A B : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (g : A ⟶ B) (hg : Function.Bijective g.hom) : A ≅ B := by
  let e : A ≃ₐ[Λ] B := AlgEquiv.ofBijective g.hom hg
  refine ⟨g, ⟨e.symm.toAlgHom, IsLocalHom.of_surjective e.symm.toRingEquiv.toRingHom
      e.symm.surjective, fun b => ?_⟩, ?_, ?_⟩
  · have hc := g.residue_comm (e.symm b)
    rw [show g.hom (e.symm b) = b from e.apply_symm_apply b] at hc
    exact hc.symm
  · exact ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a => e.symm_apply_apply a)
  · exact ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun b => e.apply_symm_apply b)

/-- The isomorphism attached to a bijective morphism has that morphism as its forward
direction. -/
@[simp]
public theorem isoOfBijectiveHom_hom {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (g : A ⟶ B)
    (hg : Function.Bijective g.hom) : (isoOfBijectiveHom g hg).hom = g := rfl

/-- The first projection of the concrete fibre square is the first coordinate. -/
public theorem pullbackFst_of_surjective_apply
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, w, w} Λ k} (g₁ : A₁ ⟶ A) (g₂ : A₂ ⟶ A)
    (h : Function.Surjective g₁.hom ∨ Function.Surjective g₂.hom)
    (t : ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ h) :
    (ArtinianLocalAlgCat.pullbackFst_of_surjective g₁ g₂ h).hom t = t.val.1 := by
  rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]; rfl

/-- The second projection of the concrete fibre square is the second coordinate. -/
public theorem pullbackSnd_of_surjective_apply
    {A₁ A₂ A : ArtinianLocalAlgCat.{u, w, w} Λ k} (g₁ : A₁ ⟶ A) (g₂ : A₂ ⟶ A)
    (h : Function.Surjective g₁.hom ∨ Function.Surjective g₂.hom)
    (t : ArtinianLocalAlgCat.pullbackObj_of_surjective g₁ g₂ h) :
    (ArtinianLocalAlgCat.pullbackSnd_of_surjective g₁ g₂ h).hom t = t.val.2 := by
  rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom]; rfl

end

/-! ### The trivial extension by the kernel as a fibre square coordinate -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
  (f : A' ⟶ A) (hf : Function.Surjective f.hom)
  (D : InfinitesimalMap f (𝟙 A')
    (ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf))
    (ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf)))

/-- The first coordinate of the difference coordinate is the residue of the trivial
extension. -/
public theorem infinitesimalMap_coordinate_fst (z : D.target) :
    (D.coordinate z).1 = D.target.residueEquiv (residue D.target z) := by
  obtain ⟨t, rfl⟩ := D.g_surjective z
  rw [D.first t, (ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)).residue_comm t]
  exact (D.g.residue_comm t).symm

/-- For a surjection of `𝒞_Λ` whose kernel `I` is annihilated by the maximal ideal of the source,
the first projection and the difference coordinate `(a₁, a₂) ↦ (ā₁, a₂ - a₁)` exhibit the concrete
fibre square `A' ×_A A'` as the fibre square of `A'` and the trivial extension `k ⊕ I` over the
residue field. -/
public theorem isPullback_infinitesimalMap :
    IsPullback (ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)) D.g
      (residueMorphism A') (residueMorphism D.target) := by
  classical
  have hker : ∀ z : D.target, f.hom ((D.coordinate z).2 : A') = 0 :=
    fun z => RingHom.mem_ker.mp (D.coordinate z).2.2
  have hid : ∀ a : A', (𝟙 A' : A' ⟶ A').hom a = a := fun _ => rfl
  have hw : ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf) ≫ residueMorphism A' =
      D.g ≫ residueMorphism D.target := hom_residueFieldObject_ext _ _
  have hsurj : Function.Surjective (residueMorphism A').hom ∨
      Function.Surjective (residueMorphism D.target).hom :=
    .inl (surjective_hom_residueMorphism A')
  have hQ := ArtinianLocalAlgCat.isPullback_of_surjective (residueMorphism A')
    (residueMorphism D.target) hsurj
  have hΦ1 := hQ.lift_fst (ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)) D.g hw
  have hΦ2 := hQ.lift_snd (ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)) D.g hw
  have hv1 : ∀ t, ((hQ.lift _ D.g hw).hom t).val.1 = t.val.1 := fun t =>
    (pullbackFst_of_surjective_apply _ _ hsurj _).symm.trans
      ((congrArg (fun q : _ ⟶ A' => q.hom t) hΦ1).trans
        (pullbackFst_of_surjective_apply f f (.inl hf) t))
  have hv2 : ∀ t, ((hQ.lift _ D.g hw).hom t).val.2 = D.g.hom t := fun t =>
    (pullbackSnd_of_surjective_apply _ _ hsurj _).symm.trans
      (congrArg (fun q : _ ⟶ D.target => q.hom t) hΦ2)
  have hbij : Function.Bijective (hQ.lift _ D.g hw).hom := by
    constructor
    · intro t s hts
      have h1 := (hv1 t).symm.trans ((congrArg (fun y => y.val.1) hts).trans (hv1 s))
      have hg := (hv2 t).symm.trans ((congrArg (fun y => y.val.2) hts).trans (hv2 s))
      have hd := congrArg Subtype.val
        ((D.second t).symm.trans
          ((congrArg (fun y => (D.coordinate y).2) hg).trans (D.second s)))
      simp only [hid, pullbackFst_of_surjective_apply, pullbackSnd_of_surjective_apply, h1] at hd
      exact Subtype.ext (Prod.ext h1 (sub_left_injective hd))
    · intro y
      obtain ⟨⟨a, z⟩, hyz⟩ := y
      have hyz' : (residueMorphism A').hom a = (residueMorphism D.target).hom z := hyz
      have hres : A'.residueEquiv (residue A' a) = (D.coordinate z).1 := by
        rw [infinitesimalMap_coordinate_fst f hf D z]
        simpa only [hom_residueMorphism_apply] using congrArg ULift.down hyz'
      have hfb : f.hom a = f.hom (a + ((D.coordinate z).2 : A')) := by
        rw [map_add, hker z, add_zero]
      let t : ArtinianLocalAlgCat.pullbackObj_of_surjective f f (.inl hf) :=
        ⟨(a, a + ((D.coordinate z).2 : A')), hfb⟩
      have hgt : D.g.hom t = z := by
        apply D.coordinate.injective
        refine Prod.ext ((D.first t).trans ?_) ((D.second t).trans (Subtype.ext ?_))
        · rw [pullbackFst_of_surjective_apply]
          exact hres
        · dsimp only
          rw [hid, pullbackFst_of_surjective_apply, pullbackSnd_of_surjective_apply]
          exact add_sub_cancel_left a _
      exact ⟨t, Subtype.ext (Prod.ext ((hv1 t)) ((hv2 t).trans hgt))⟩
  refine hQ.of_iso' (isoOfBijectiveHom _ hbij) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_ <;> simp [hΦ1, hΦ2]

/-- For a surjection of `𝒞_Λ` whose kernel `I` is annihilated by the maximal ideal of the source
and any fibre square of `A'` with itself over `A`, the first projection and a coordinate into the
trivial extension `k ⊕ I` form a fibre square over the residue field. -/
public theorem exists_isPullback_kernelTrivialExtension
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    {Y : ArtinianLocalAlgCat.{u, w, w} Λ k} {pr₁ pr₂ : Y ⟶ A'}
    (hPB : IsPullback pr₁ pr₂ f f) :
    ∃ γ : Y ⟶ (infinitesimalDifferenceMap f hf hann).target,
      IsPullback pr₁ γ (residueMorphism A')
        (residueMorphism (infinitesimalDifferenceMap f hf hann).target) := by
  have hconc := ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)
  refine ⟨(hPB.isoIsPullback A' A' hconc).hom ≫ (infinitesimalDifferenceMap f hf hann).g, ?_⟩
  refine (isPullback_infinitesimalMap f hf (infinitesimalDifferenceMap f hf hann)).of_iso'
    (hPB.isoIsPullback A' A' hconc) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp

end

/-! ### The action of the infinitesimal automorphisms of the trivial extension -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- For a category cofibered in groupoids over `𝒞_Λ` satisfying (RS), a morphism `x' ⟶ x` lying
over a surjection whose kernel `I` is annihilated by the maximal ideal, and a pushforward `x₀` of
`x'` to the special fibre, pushforward along the difference coordinate identifies the automorphisms
of an (RS) fibre square of `x'` with itself over `x` that are trivial on the first projection with
the infinitesimal automorphisms, relative to `x₀`, of a pushforward of that square to the trivial
extension `k ⊕ I`. -/
public theorem exists_relativeInfinitesimalAutomorphisms_kernelTrivialExtension_mulEquiv
    (hrs : SatisfiesRS p) {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x' : p.Fiber A'} {x : p.Fiber A}
    (g : A' ⟶ A) (φ : x'.1 ⟶ x.1) (hφ : p.IsHomLift g φ)
    (hg : Function.Surjective g.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker g.hom.toRingHom, a * (i : A') = 0)
    {x₀ : p.Fiber (residueFieldObject.{u, w, w} Λ k)}
    (φ₀ : x'.1 ⟶ x₀.1) (hφ₀ : p.IsHomLift (residueMorphism A') φ₀) :
    ∃ (Z : F) (π : p.obj Z ⟶ A') (c : Z ⟶ x'.1) (hc : p.IsHomLift π c)
      (xI : p.Fiber (infinitesimalDifferenceMap g hg hann).target) (fI : xI.1 ⟶ x₀.1)
      (hfI : p.IsHomLift
        (residueMorphism (infinitesimalDifferenceMap g hg hann).target) fI)
      (_ : ↥(relativeInfinitesimalAutomorphisms (x' := ⟨Z, rfl⟩) (x := x') hrs.1 π c hc) ≃*
        ↥(relativeInfinitesimalAutomorphisms hrs.1
          (residueMorphism (infinitesimalDifferenceMap g hg hann).target) fI hfI))
      (act : ↥(relativeInfinitesimalAutomorphisms (x' := ⟨Z, rfl⟩) (x := x') hrs.1 π c hc) →
          ↥(relativeInfinitesimalAutomorphisms hrs.1 g φ hφ) →
          ↥(relativeInfinitesimalAutomorphisms hrs.1 g φ hφ)),
      (∀ s, act 1 s = s) ∧
      (∀ a b s, act (a * b) s = act a (act b s)) ∧
      (∀ s, Function.Bijective fun a => act a s) := by
  obtain ⟨X', rfl⟩ := x'
  obtain ⟨X, rfl⟩ := x
  have := hφ
  obtain rfl : g = p.map φ := IsHomLift.eq_of_isHomLift p g φ
  obtain ⟨cone, ⟨hlim⟩, ⟨hlimp⟩⟩ := hrs.2 φ φ hg
  have hsq : IsPullback cone.fst cone.snd φ φ := IsPullback.of_isLimit hlim
  have hbase0 : IsPullback (p.map cone.fst) (p.map cone.snd) (p.map φ) (p.map φ) :=
    IsPullback.of_isLimit hlimp
  obtain ⟨γ, hbase⟩ :=
    exists_isPullback_kernelTrivialExtension (p.map φ) hg hann hbase0
  obtain ⟨XI, cI, hcI⟩ := exists_pushforward hrs.1 γ cone.pt rfl
  let xI : p.Fiber (infinitesimalDifferenceMap (p.map φ) hg hann).target :=
    ⟨XI, IsHomLift.codomain_eq p γ cI⟩
  let := hcI
  let := hφ₀
  let := IsHomLift.map p cone.fst
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hrs.1 γ cI hcI
  let fI : XI ⟶ x₀.1 := Functor.IsStronglyCocartesian.map p γ cI hbase.w (cone.fst ≫ φ₀)
  have hfac : cI ≫ fI = cone.fst ≫ φ₀ :=
    Functor.IsStronglyCocartesian.fac p γ cI hbase.w (cone.fst ≫ φ₀)
  have hfI : p.IsHomLift
      (residueMorphism (infinitesimalDifferenceMap (p.map φ) hg hann).target) fI :=
    inferInstance
  let := hfI
  have hbaseI : IsPullback (p.map cone.fst) (p.map cI) (p.map φ₀) (p.map fI) := by
    refine hbase.of_iso (Iso.refl _) (Iso.refl _) (eqToIso xI.2.symm) (eqToIso x₀.2.symm)
      ?_ ?_ ?_ ?_
    · simp
    · rw [IsHomLift.fac' p γ cI]; simp
    · rw [IsHomLift.fac' p (residueMorphism (p.obj X')) φ₀]; simp
    · rw [IsHomLift.fac' p
        (residueMorphism (infinitesimalDifferenceMap (p.map φ) hg hann).target) fI]
      simp
  have hsurjI : Function.Surjective (p.map fI).hom := by
    rw [IsHomLift.fac' p
      (residueMorphism (infinitesimalDifferenceMap (p.map φ) hg hann).target) fI]
    exact (surjective_hom_eqToHom _).comp
      ((surjective_hom_residueMorphism _).comp (surjective_hom_eqToHom _))
  obtain ⟨hlimI⟩ := isLimit_of_map_isLimit hrs φ₀ fI
    (PullbackCone.mk cone.fst cI hfac.symm) hsurjI
    ⟨IsLimit.ofIsoLimit hbaseI.isLimit
      (PullbackCone.ext (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm)⟩
  have hsqI : IsPullback cone.fst cI φ₀ fI := IsPullback.of_isLimit hlimI
  let E := relativeInfinitesimalAutomorphismsFibreSquareEquiv
    (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨X', rfl⟩) (x₂ := xI) (x := x₀)
    hrs.1 (IsHomLift.map p cone.fst) hcI hfI hsqI hbase
  let := relativeInfinitesimalAutomorphismsFibreSquareAction
    (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨X', rfl⟩) (x₂ := ⟨X', rfl⟩) (x := ⟨X, rfl⟩)
    hrs.1 (IsHomLift.map p cone.fst) (IsHomLift.map p cone.snd) (IsHomLift.map p φ) hsq hbase0
  have hbij := relativeInfinitesimalAutomorphismsFibreSquareAction_bijective
    (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨X', rfl⟩) (x₂ := ⟨X', rfl⟩) (x := ⟨X, rfl⟩)
    hrs.1 (IsHomLift.map p cone.fst) (IsHomLift.map p cone.snd) (IsHomLift.map p φ) hsq hbase0
  exact ⟨cone.pt, p.map cone.fst, cone.fst, IsHomLift.map p cone.fst, xI, fI, hfI, E,
    fun a s => a • s, fun s => one_smul _ s, fun a b s => mul_smul a b s, hbij⟩

/-- For a category cofibered in groupoids over `𝒞_Λ` satisfying (RS) and a morphism `x' ⟶ x` lying
over a surjection whose kernel `I` is annihilated by the maximal ideal, the group `Inf(x'/x)`
carries a free and transitive action by the infinitesimal automorphisms, relative to a pushforward
`x₀` of `x'` to the special fibre, of a pushforward of an (RS) fibre square of `x'` with itself
over `x` to the trivial extension `k ⊕ I`. -/
public theorem exists_relativeInfinitesimalAutomorphisms_kernelTrivialExtension_action
    (hrs : SatisfiesRS p) {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x' : p.Fiber A'} {x : p.Fiber A}
    (g : A' ⟶ A) (φ : x'.1 ⟶ x.1) (hφ : p.IsHomLift g φ)
    (hg : Function.Surjective g.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker g.hom.toRingHom, a * (i : A') = 0)
    {x₀ : p.Fiber (residueFieldObject.{u, w, w} Λ k)}
    (φ₀ : x'.1 ⟶ x₀.1) (hφ₀ : p.IsHomLift (residueMorphism A') φ₀) :
    ∃ (xI : p.Fiber (infinitesimalDifferenceMap g hg hann).target) (fI : xI.1 ⟶ x₀.1)
      (hfI : p.IsHomLift
        (residueMorphism (infinitesimalDifferenceMap g hg hann).target) fI)
      (act : ↥(relativeInfinitesimalAutomorphisms hrs.1
            (residueMorphism (infinitesimalDifferenceMap g hg hann).target) fI hfI) →
          ↥(relativeInfinitesimalAutomorphisms hrs.1 g φ hφ) →
          ↥(relativeInfinitesimalAutomorphisms hrs.1 g φ hφ)),
      (∀ s, act 1 s = s) ∧
      (∀ a b s, act (a * b) s = act a (act b s)) ∧
      (∀ s, Function.Bijective fun a => act a s) := by
  obtain ⟨Z, π, c, hc, xI, fI, hfI, E, act, hone, hmul, hbij⟩ :=
    exists_relativeInfinitesimalAutomorphisms_kernelTrivialExtension_mulEquiv
      hrs g φ hφ hg hann φ₀ hφ₀
  refine ⟨xI, fI, hfI, fun a s => act (E.symm a) s, fun s => ?_, fun a b s => ?_,
    fun s => (hbij s).comp E.symm.bijective⟩
  · simp only [map_one]
    exact hone s
  · simp only [map_mul]
    exact hmul _ _ s

end

end Deformation

end
