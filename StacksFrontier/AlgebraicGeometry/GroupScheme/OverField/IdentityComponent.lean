module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.IrreducibleComponentsBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed

/-!
# The irreducible component through the identity of a group scheme

A group scheme over a field has exactly one irreducible component containing its identity.
Over an algebraically closed field the two reduced closed subschemes cut out by two such
components multiply into an irreducible scheme dominating both, which forces them to agree;
the general case follows by base change to an algebraic closure.

## Main definitions

* `AlgebraicGeometry.componentIdeal` is the reduced ideal sheaf cutting out an irreducible
  component.
* `AlgebraicGeometry.identityPoint` is the identity point of a group scheme over a field.

## Main results

* `AlgebraicGeometry.existsUnique_irreducibleComponent_containing_identity` gives the unique
  irreducible component through the identity of a group scheme over a field.
* `AlgebraicGeometry.existsUnique_irreducibleComponent_containing_identityPoint` is the same
  statement for a bundled group object over an algebraically closed field.

## Implementation notes

A group scheme over `k` is represented by a scheme `G`, its structure morphism
`f : G ⟶ Spec k`, and a group-object structure on `Over.mk f`.  The identity point is the image
under the unit section of the closed point of the spectrum of the field, which is also the
unique point of that spectrum; for a bundled `Grp (Over (Spec (.of k)))` the two descriptions
are identified by `Subsingleton.elim`.

## References

* [Stacks Project, Tag 047M](https://stacks.math.columbia.edu/tag/047M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

universe u

/-- The ideal sheaf cutting out an irreducible component of a scheme, with its reduced
structure. -/
noncomputable def componentIdeal {X : Scheme.{u}} (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩

/-- The closed immersion of an irreducible component, with its reduced structure, into the
ambient scheme. -/
private noncomputable def componentInclusion {X : Scheme.{u}} (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) : (componentIdeal Z hZ).subscheme ⟶ X :=
  (componentIdeal Z hZ).subschemeι

/-- The reduced closed subscheme on an irreducible component has that component as its
image. -/
private lemma componentInclusion_range {X : Scheme.{u}} (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) :
    Set.range (componentInclusion Z hZ) = Z := by
  change Set.range ((componentIdeal Z hZ).subschemeι) = Z
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [componentIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- An irreducible component through the identity of a group scheme over a field is the image of
an irreducible closed subscheme over the base, containing the identity section. -/
private theorem exists_irreducible_subobject_through_identity
    {k : Type u} [Field k] {G : Scheme.{u}}
    (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    (Z : irreducibleComponents G)
    (hx : (η[Over.mk f]).left (IsLocalRing.closedPoint k) ∈ (Z : Set G)) :
    ∃ (T : Over (Spec (.of k))) (j : T ⟶ Over.mk f) (s : 𝟙_ (Over (Spec (.of k))) ⟶ T),
      s ≫ j = η[Over.mk f] ∧ Set.range j.left.base = (Z : Set G) ∧ IrreducibleSpace T.left := by
  classical
  let _ : Subsingleton (Spec (.of k)) := by
    change Subsingleton (PrimeSpectrum k)
    infer_instance
  let U := Over.mk f
  let p : Spec (.of k) ⟶ G :=
    (Over.tensorUnit_left (C := Scheme) (X := Spec (.of k))).symm ▸ (η[U]).left
  have hp : p ≫ f = 𝟙 (Spec (.of k)) := by
    dsimp [p]
    exact Over.Hom.w (η[U])
  have : IsClosedImmersion p :=
    isClosedImmersion_of_comp_eq_id f p hp
  let x : G := p (default : Spec (.of k))
  have hx' : x ∈ (Z : Set G) := by
    have : x = (η[U]).left (IsLocalRing.closedPoint k) := by
      dsimp [x, p]
      congr 1
      exact Subsingleton.elim _ _
    exact this ▸ hx
  have hrange : Set.range p = {x} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have hz : z = (default : Spec (.of k)) := Subsingleton.elim _ _
      simp [x, hz]
    · intro hy
      subst y
      exact ⟨default, rfl⟩
  let I : G.IdealSheafData := componentIdeal (Z : Set G) Z.2
  have hpSupport : p.ker.support ≤ I.support := by
    change (p.ker.support : Set G) ⊆ (Z : Set G)
    rw [Scheme.Hom.support_ker p]
    exact closure_minimal (by
      rw [hrange]
      exact Set.singleton_subset_iff.mpr hx')
      (isClosed_of_mem_irreducibleComponents _ Z.2)
  have : IsReduced p.ker.subscheme := by
    have : IsIso p.toImage := inferInstance
    exact ObjectProperty.IsClosedUnderIsomorphisms.of_iso (asIso p.toImage)
      (inferInstance : IsReduced (Spec (.of k)))
  have hpker : p.ker = Scheme.IdealSheafData.vanishingIdeal p.ker.support :=
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
      p.ker p.ker.support rfl
  have hker : I.subschemeι.ker ≤ p.ker := by
    rw [I.ker_subschemeι, hpker]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono hpSupport
  let s : Spec (.of k) ⟶ I.subscheme := IsClosedImmersion.lift I.subschemeι p hker
  have hs : s ≫ I.subschemeι = p := IsClosedImmersion.lift_fac _ _ _
  let T : Over (Spec (.of k)) := Over.mk (I.subschemeι ≫ f)
  let s' : (𝟙_ (Over (Spec (.of k)))) ⟶ T :=
    Over.homMk ((Over.tensorUnit_left (C := Scheme) (X := Spec (.of k))).symm ▸ s) (by
      change ((Over.tensorUnit_left (C := Scheme) (X := Spec (.of k))).symm ▸ s) ≫
        (I.subschemeι ≫ f) = (𝟙_ (Over (Spec (.of k)))).hom
      rw [← Category.assoc, hs]
      exact hp)
  refine ⟨T, Over.homMk I.subschemeι, s', ?_, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change (((Over.tensorUnit_left (C := Scheme) (X := Spec (.of k))).symm ▸ s) ≫
      I.subschemeι) = (η[U]).left
    simpa [← hs]
  · exact componentInclusion_range (Z : Set G) Z.2
  · let htop : I.subscheme ≃ₜ (Z : Set G) :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso I.subschemeIso)).trans
        I.gluedHomeo |>.trans
          (Homeomorph.setCongr (Scheme.IdealSheafData.coe_support_vanishingIdeal _))
    exact (htop.irreducibleSpace_iff).2 (Subtype.irreducibleSpace Z.2.1)

/-- Over an algebraically closed field, two irreducible components of a group scheme that both
contain the identity point coincide. -/
private theorem unique_identity_component_over_algClosed
    {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (.of k)) [GrpObj (Over.mk f)]
    (Z₁ Z₂ : irreducibleComponents G)
    (he₁ : (η[Over.mk f]).left (IsLocalRing.closedPoint k) ∈ (Z₁ : Set G))
    (he₂ : (η[Over.mk f]).left (IsLocalRing.closedPoint k) ∈ (Z₂ : Set G)) :
    Z₁ = Z₂ := by
  let U := Over.mk f
  obtain ⟨T₁, j₁, s₁', hs₁', hr₁, _⟩ := exists_irreducible_subobject_through_identity f Z₁ he₁
  obtain ⟨T₂, j₂, s₂', hs₂', hr₂, _⟩ := exists_irreducible_subobject_through_identity f Z₂ he₂
  let P := T₁ ⊗ T₂
  have : IrreducibleSpace P.left := by
    change IrreducibleSpace ↥(pullback T₁.hom T₂.hom)
    let _ : GeometricallyIrreducible T₁.hom :=
      geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k _ _
    infer_instance
  let m : P ⟶ U := (j₁ ⊗ₘ j₂) ≫ μ[U]
  let q₁ : T₁ ⟶ P := (ρ_ T₁).inv ≫ (𝟙 T₁ ⊗ₘ s₂')
  let q₂ : T₂ ⟶ P := (λ_ T₂).inv ≫ (s₁' ⊗ₘ 𝟙 T₂)
  have hq₁ : q₁ ≫ m = j₁ := by
    dsimp [q₁, m]
    let A := 𝟙 T₁ ⊗ₘ s₂'
    let B := j₁ ⊗ₘ j₂
    have hAB : A ≫ B = j₁ ⊗ₘ η[U] := by
      dsimp [A, B]
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp [hs₂']
    calc
      ((ρ_ T₁).inv ≫ A) ≫ B ≫ μ[U] = (ρ_ T₁).inv ≫ (A ≫ B) ≫ μ[U] := by
        simp [Category.assoc]
      _ = (ρ_ T₁).inv ≫ (j₁ ⊗ₘ η[U]) ≫ μ[U] := by rw [hAB]
      _ = (ρ_ T₁).inv ≫ (ρ_ T₁).hom ≫ j₁ := by rw [MonObj.mul_one_hom]
      _ = j₁ := by simp
  have hq₂ : q₂ ≫ m = j₂ := by
    dsimp [q₂, m]
    let A := s₁' ⊗ₘ 𝟙 T₂
    let B := j₁ ⊗ₘ j₂
    have hAB : A ≫ B = η[U] ⊗ₘ j₂ := by
      dsimp [A, B]
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp [hs₁']
    calc
      ((λ_ T₂).inv ≫ A) ≫ B ≫ μ[U] = (λ_ T₂).inv ≫ (A ≫ B) ≫ μ[U] := by
        simp [Category.assoc]
      _ = (λ_ T₂).inv ≫ (η[U] ⊗ₘ j₂) ≫ μ[U] := by rw [hAB]
      _ = (λ_ T₂).inv ≫ (λ_ T₂).hom ≫ j₂ := by rw [MonObj.one_mul_hom]
      _ = j₂ := by simp
  have himage {T : Over (Spec (.of k))} (j : T ⟶ U) (q : T ⟶ P) (hq : q ≫ m = j) :
      Set.range j.left.base ⊆ Set.range m.left.base := by
    rintro y ⟨z, rfl⟩
    refine ⟨q.left.base z, ?_⟩
    have h := congrArg (fun t : T ⟶ U => t.left.base z) hq
    simpa [Scheme.Hom.comp_base] using h
  have himage₁ := himage j₁ q₁ hq₁
  have himage₂ := himage j₂ q₂ hq₂
  rw [hr₁] at himage₁
  rw [hr₂] at himage₂
  have himageIrred : IsIrreducible (Set.range m.left.base) := by
    simpa using (IrreducibleSpace.isIrreducible_univ P.left).image m.left.base
      m.left.continuous.continuousOn
  have hclosure : (Z₁ : Set G) = closure (Set.range m.left.base) :=
    Z₁.2.eq_of_subset himageIrred.closure (himage₁.trans subset_closure)
  have hZ₂Z₁ : (Z₂ : Set G) ⊆ (Z₁ : Set G) := by
    rw [hclosure]
    exact himage₂.trans subset_closure
  exact Subtype.ext ((Z₂.2).eq_of_subset Z₁.2.1 hZ₂Z₁).symm

/-- The identity point of a group scheme over a field. -/
noncomputable abbrev identityPoint (k : Type u) [Field k]
    (G : Grp (Over (Spec (.of k)))) : G.X.left :=
  (η[G.X]).left
    ((Over.tensorUnit_left (C := Scheme) (X := Spec (.of k))).symm ▸
      (default : Spec (.of k)))

/-- The projection of a base change identifies the identity points of the two group
schemes. -/
theorem identityPoint_baseChange_fst
    (R S : Type u) [Field R] [Field S] [Algebra R S]
    (G : Grp (Over (Spec (.of R)))) :
    (pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S)))).base
      (identityPoint S ((Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj G)) =
      identityPoint R G := by
  let _ : GrpObj (Over.mk G.X.hom) := G.grp
  let g := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let _ : GrpObj (Over.mk (pullback.snd G.X.hom g)) := Over.grpObjMkPullbackSnd
  let unit := η[Over.mk (pullback.snd G.X.hom g)].left
  have hfst : unit ≫ pullback.fst G.X.hom g = g ≫ η[G.X].left := by
    dsimp [unit]
    rw [CategoryTheory.Over.grpObjMkPullbackSnd_one,
      CategoryTheory.Over.comp_left, CategoryTheory.Over.ε_pullback_left]
    change (inv (pullback.snd (𝟙 (Spec (.of R))) g) ≫
        ((Over.pullback g).map (η[G.X])).left) ≫ pullback.fst G.X.hom g = _
    dsimp [CategoryTheory.Over.pullback]
    have hproj : inv (pullback.snd (𝟙 (Spec (.of R))) g) ≫
        pullback.fst (𝟙 (Spec (.of R))) g = g := by
      have hc := pullback.condition (f := (𝟙 (Spec (.of R)))) (g := g)
      have hfsteq : pullback.fst (𝟙 (Spec (.of R))) g =
          pullback.snd (𝟙 (Spec (.of R))) g ≫ g := by simpa using hc
      rw [hfsteq]
      simp
    change (inv (pullback.snd (𝟙 (Spec (.of R))) g) ≫
      pullback.lift (pullback.fst (𝟙 (Spec (.of R))) g ≫ η[G.X].left)
        (pullback.snd (𝟙 (Spec (.of R))) g) _ ≫ pullback.fst G.X.hom g) = _
    rw [pullback.lift_fst, ← Category.assoc, hproj]
  let eS := (Over.tensorUnit_left (C := Scheme) (X := Spec (.of S))).symm ▸
    (default : Spec (.of S))
  let eR := (Over.tensorUnit_left (C := Scheme) (X := Spec (.of R))).symm ▸
    (default : Spec (.of R))
  have hpt := congrArg (fun q => (Scheme.forget.map q) eS) hfst
  have hpt' : (Scheme.forget.map (pullback.fst G.X.hom g))
        ((Scheme.forget.map unit) eS) =
      (Scheme.forget.map η[G.X].left) ((Scheme.forget.map g) eS) := by
    simpa only [Functor.map_comp, CategoryTheory.comp_apply] using hpt
  have : Subsingleton (Scheme.forget.obj (Spec (.of R))) := by
    change Subsingleton (PrimeSpectrum R)
    infer_instance
  have hspec : (Scheme.forget.map g) eS = eR := Subsingleton.elim _ _
  change (Scheme.forget.map (pullback.fst G.X.hom g)) ((Scheme.forget.map unit) eS) =
    (Scheme.forget.map η[G.X].left) eR
  rwa [hspec] at hpt'

/-- **Stacks Project, Tag 047M.** A group scheme over a field has a unique irreducible
component containing its identity point. -/
@[stacks 047M "identity_component_unique",
  sga "3 VIA 2.4" "(i) irred., base field",
  sga "3 VIA 2.6.5" "(a)"]
theorem existsUnique_irreducibleComponent_containing_identity
    {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
    [GrpObj (Over.mk f)] :
    ∃! Z : irreducibleComponents G,
      (η[Over.mk f]).left (IsLocalRing.closedPoint k) ∈ (Z : Set G) := by
  classical
  let x : G := (η[Over.mk f]).left (IsLocalRing.closedPoint k)
  let Z₀ : irreducibleComponents G :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hx₀ : x ∈ (Z₀ : Set G) := mem_irreducibleComponent
  refine ⟨Z₀, hx₀, fun Z hZ => ?_⟩
  let Ω := AlgebraicClosure k
  let _ : Algebra k Ω := inferInstance
  let _ : IsAlgClosed Ω := AlgebraicClosure.isAlgClosed k
  let g : Spec (.of Ω) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let XΩ : Scheme := pullback (C := Scheme) f g
  let π : XΩ ⟶ G := pullback.fst f g
  let fΩ : XΩ ⟶ Spec (.of Ω) := pullback.snd f g
  let _ : GrpObj (Over.mk fΩ) := Over.grpObjMkPullbackSnd
  let G₀ : Grp (Over (Spec (.of k))) := Grp.mk (Over.mk f)
  let GΩ : Grp (Over (Spec (.of Ω))) := (Over.pullback g).mapGrp.obj G₀
  let xΩ : XΩ := (η[Over.mk fΩ]).left (IsLocalRing.closedPoint Ω)
  have hidentity : π.base xΩ = x := by
    have hbar : identityPoint Ω GΩ = xΩ := by
      dsimp [identityPoint, GΩ, G₀, xΩ, fΩ]
      congr 1
      let _ : Subsingleton (Spec (.of Ω)) := by
        change Subsingleton (PrimeSpectrum Ω)
        infer_instance
      exact Subsingleton.elim _ _
    have hk : identityPoint k G₀ = x := by
      dsimp [identityPoint, G₀, x]
      congr 1
      let _ : Subsingleton (Spec (.of k)) := by
        change Subsingleton (PrimeSpectrum k)
        infer_instance
      exact Subsingleton.elim _ _
    rw [← hbar, ← hk]
    simpa [G₀, GΩ, g, π, XΩ, fΩ] using
      (identityPoint_baseChange_fst k Ω G₀)
  have hcomponent_eq (W₁ W₂ : irreducibleComponents G)
      (h₁ : x ∈ (W₁ : Set G)) (h₂ : x ∈ (W₂ : Set G)) : W₁ = W₂ := by
    have baseChangeComponent (W : irreducibleComponents G)
        (hW : x ∈ (W : Set G)) :
        ∃ D : irreducibleComponents XΩ,
          xΩ ∈ (D : Set XΩ) ∧ (D : Set XΩ) ⊆ π.base ⁻¹' (W : Set G) := by
      have hpre := preimage_irreducibleComponent_eq_sUnion k Ω G f (W : Set G) W.2
      have hxpre : xΩ ∈ π.base ⁻¹' (W : Set G) := by
        change π.base xΩ ∈ (W : Set G)
        rw [hidentity]
        exact hW
      rw [hpre] at hxpre
      obtain ⟨D, hD, hxD⟩ := Set.mem_sUnion.mp hxpre
      exact ⟨⟨D, hD.1⟩, hxD, hD.2⟩
    obtain ⟨D₁, hxD₁, hD₁⟩ := baseChangeComponent W₁ h₁
    obtain ⟨D₂, hxD₂, hD₂⟩ := baseChangeComponent W₂ h₂
    have hD : D₁ = D₂ :=
      unique_identity_component_over_algClosed fΩ D₁ D₂ (by
        change xΩ ∈ (D₁ : Set XΩ)
        exact hxD₁) (by
        change xΩ ∈ (D₂ : Set XΩ)
        exact hxD₂)
    subst D₂
    have himage (W : irreducibleComponents G) (hD : (D₁ : Set XΩ) ⊆ π.base ⁻¹' (W : Set G)) :
        π.base '' (D₁ : Set XΩ) = (W : Set G) :=
      Set.Subset.antisymm (Set.image_subset_iff.mpr hD)
        ((mapsTo_irreducibleComponents_baseChange k Ω G f D₁.2).2 W.2.1
          (Set.image_subset_iff.mpr hD))
    exact Subtype.ext ((himage W₁ hD₁).symm.trans (himage W₂ hD₂))
  exact (hcomponent_eq Z₀ Z hx₀ hZ).symm

/-- A group scheme over an algebraically closed field has exactly one irreducible component
containing its identity point. -/
theorem existsUnique_irreducibleComponent_containing_identityPoint
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) :
    ∃! Z : irreducibleComponents G.X.left, identityPoint k G ∈ (Z : Set G.X.left) := by
  have h : (default : Spec (.of k)) = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  simpa [identityPoint, h] using
    (let _ : GrpObj (Over.mk G.X.hom) := G.grp
     existsUnique_irreducibleComponent_containing_identity
       (G.X.hom : G.X.left ⟶ Spec (.of k)))

end AlgebraicGeometry

end
