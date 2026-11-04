module

public import StacksFrontier.Deformation.Artin.Versality.Openness
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldVersalLift

/-!
# The category of the openness-of-versality example

Tag 07XR builds, over `S = Spec k[s, t]`, the full subcategory `𝒳` of the big fppf site on
those schemes admitting an affine open covering whose coordinate rings `A` satisfy the
finitary condition `A = (s, t, f_1, …, f_n)` with `f_i s = 0`
(`Deformation.Artin.IsAdmissible`), and asserts that `𝒳` fails openness of versality: over
the slice `U = Spec k[s, t]/(s)` there is an object versal at the origin and at no other
point.

This file proves those two assertions. The object is the slice itself. **Versality at the
origin**: an object of `𝒳` lying over `Spec B` with `B` Artinian local has `s = 0` in `B`,
because `s` and `t` both land in the maximal ideal of `B` — they die in the residue field of
the slice at the origin — and the condition of Tag 07XR then forces `s = 0`; so the
structure morphism of `Spec B` factors through the slice, and that factorization is the
required lift, uniquely, because the slice immersion is a monomorphism. **Non-versality
elsewhere**: at a point `u` where `t` does not vanish — that is, at every point other than
the origin, since the origin is the only prime of `k[t]` containing `t` — the element `t`
becomes a unit in every Artinian local algebra over the local ring of the base, so the dual
numbers `κ(u)[ε]` with `s` acting as `ε` are an object of `𝒳`; the lifting problem along
`κ(u)[ε] → κ(u)` has no solution, since a solution would factor the structure morphism of
`Spec κ(u)[ε]` through the slice and force `s = 0` there. Openness of versality then fails
because every open neighbourhood of the origin contains another closed point, the slice
being a Jacobson scheme with a generic point.

This file also analyses that condition on a local ring and identifies the objects of `𝒳` with
affine coordinate ring, which is where the example's assertions about `𝒳` are read. The
condition is **finitary and local**: in a local ring in which neither `s` nor `t` is a unit it
says exactly that `s = 0`, since one of the `f_i` must then be a unit and kills `s`. On an
affine scheme the condition on the covering can therefore be tested on the coordinate ring
itself, and for an Artinian local coordinate ring it is equivalent to it — the spectrum is one
point, so the member of the covering that contains that point is the whole spectrum.

The slice `U = Spec k[s, t]/(s)`, on which `s` vanishes identically, is accordingly an object
of `𝒳`, and the origin `u₀ = (s, t)` is a closed point of it.

## Main definitions

* `Deformation.Artin.specAlgebra` — the `k[s,t]`-algebra structure on a ring read off a
  morphism of its spectrum to `Spec k[s,t]`, which is the structure in which the condition of
  Tag 07XR is stated for an affine object.
* `Deformation.Artin.sliceRing`, `Deformation.Artin.sliceImmersion` — the ring `k[s,t]/(s)`
  and the closed immersion of its spectrum into `Spec k[s,t]`.
* `Deformation.Artin.sliceObject` — the slice as an object of the category of Tag 07XR, and
  `Deformation.Artin.artinAxiomsOver` the structure functor of that category to schemes over
  `S`.
* `Deformation.Artin.slicePoint` — the origin `u₀ = (s, t)` of the slice.

## Main results

* `Deformation.Artin.isAdmissible_of_eq_zero` and
  `Deformation.Artin.eq_zero_of_isAdmissible` — the condition of Tag 07XR holds in a local
  ring in which `s` and `t` are not units exactly when `s = 0` there.
* `Deformation.Artin.isAdmissible_of_ringHom` — the condition passes along a map of
  `k[s,t]`-algebras.
* `Deformation.Artin.isArtinAxiomsObject_siteObject` and
  `Deformation.Artin.isAdmissible_of_isArtinAxiomsObject` — an affine scheme over
  `Spec k[s,t]` is an object of the category when its coordinate ring satisfies the
  condition, and conversely its coordinate ring satisfies the condition when the ring is
  Artinian local.
* `Deformation.Artin.isMaximal_slicePoint`, `Deformation.Artin.mk_X_mem_slicePoint` — the
  origin is a closed point of the slice, and both coordinates vanish there.
* `Deformation.Artin.isVersalAt_sliceObject` — the slice is versal at the origin, and
  `Deformation.Artin.not_isVersalAt_sliceObject` — it is versal at no other point.
* `Deformation.Artin.not_isOpenVersality_artinAxiomsCategory` — the category of Tag 07XR
  therefore fails openness of versality, which is axiom [5].

## Implementation notes

For an affine object the algebra structure in which the condition is read is the one induced
by the structure morphism, through the identification of the global sections of a spectrum
with the ring. Admissibility is therefore transported along ring maps with the two algebra
structures supplied as explicit data rather than as instances, so that the structure coming
from a scheme morphism can be compared with a structure given by a ring homomorphism. In the
converse direction the member of the covering containing the one point of an Artinian local
spectrum is identified with the whole spectrum by `isoOfRangeEq`, rather than by an equality
of schemes, so that the comparison applies to an object whose underlying scheme is merely
isomorphic to a spectrum.

Openness of versality is stated by `Deformation.Artin.IsOpenVersality`, whose argument is a
category fibred in groupoids over `Over S`; the structure functor of a size-bounded big fppf
subcategory is not fibred in groupoids over `Over S`, so the failure is stated in the
written-out form of that predicate, with
`Deformation.Artin.isOpenVersality_eq_written_out` recording that the two agree.

The `k[s,t]`-algebra structures on the Artinian local algebras met in the versality condition
are read through the local ring of `Spec k[s,t]` at the image of the point, and are therefore
supplied as explicit data rather than as instances: the local ring is a colimit, and instance
search on it does not see through to the structure a scheme morphism induces. For the same
reason the dual numbers are formed over the residue field *as a module over itself in the
sense of the site*, so that the square-zero ring structures of this file and of
`Deformation.Artin.squareZeroArtinianObj` are the same ones. The extension of the structure
map to the local ring is by `IsLocalization.lift`: every element not vanishing at the point
becomes a unit in the dual numbers, since its image has invertible first component.

## References

* [Stacks Project, Tag 07XR](https://stacks.math.columbia.edu/tag/07XR)
-/
@[expose] public section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

universe u v

variable {k : Type u} [Field k]

/-! ### Admissibility over a local ring -/

/-- An algebra in which `s` vanishes is admissible. -/
public theorem isAdmissible_of_eq_zero (A : Type v) [CommRing A]
    [Algebra (MvPolynomial (Fin 2) k) A]
    (hs : algebraMap (MvPolynomial (Fin 2) k) A (X 0) = 0) : IsAdmissible k A := by
  refine ⟨1, fun _ => 1, 0, 0, fun _ => 1, by simp, fun i => by simp [hs]⟩

/-- In a local algebra in which `s` and `t` are not units, admissibility forces `s = 0`. -/
public theorem eq_zero_of_isAdmissible (A : Type v) [CommRing A] [IsLocalRing A]
    [Algebra (MvPolynomial (Fin 2) k) A]
    (hs : algebraMap (MvPolynomial (Fin 2) k) A (X 0) ∈ IsLocalRing.maximalIdeal A)
    (ht : algebraMap (MvPolynomial (Fin 2) k) A (X 1) ∈ IsLocalRing.maximalIdeal A)
    (h : IsAdmissible k A) : algebraMap (MvPolynomial (Fin 2) k) A (X 0) = 0 := by
  obtain ⟨n, f, a, b, g, hgen, hann⟩ := h
  by_cases hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal A
  · exfalso
    have hone : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [← hgen]
      exact Submodule.add_mem _ (Submodule.add_mem _
        (Ideal.mul_mem_right _ _ hs) (Ideal.mul_mem_right _ _ ht))
        (Submodule.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hf i))
    exact (Ideal.eq_top_iff_one _).not.mp
      (IsLocalRing.maximalIdeal.isMaximal A).ne_top hone
  · obtain ⟨i, hi⟩ := not_forall.mp hf
    obtain ⟨w, hw⟩ := (IsLocalRing.notMem_maximalIdeal.mp hi).exists_left_inv
    calc algebraMap (MvPolynomial (Fin 2) k) A (X 0)
        = w * (f i * algebraMap (MvPolynomial (Fin 2) k) A (X 0)) := by
          rw [← mul_assoc, hw, one_mul]
      _ = 0 := by rw [hann i, mul_zero]

/-- Admissibility is inherited along a map of algebras, stated for the two algebra
structures as data so that it can be applied to structures read off a scheme morphism. -/
public theorem isAdmissible_of_ringHom {A A' : Type v} [CommRing A] [CommRing A']
    (inst : Algebra (MvPolynomial (Fin 2) k) A)
    (inst' : Algebra (MvPolynomial (Fin 2) k) A') (ψ : A →+* A')
    (hψ : ∀ r, ψ (algebraMap (MvPolynomial (Fin 2) k) A r) =
      algebraMap (MvPolynomial (Fin 2) k) A' r)
    (hA : @IsAdmissible k _ A _ inst) : @IsAdmissible k _ A' _ inst' := by
  obtain ⟨n, f, a, b, g, hgen, hann⟩ := hA
  refine ⟨n, fun i => ψ (f i), ψ a, ψ b, fun i => ψ (g i), ?_, fun i => ?_⟩
  · simpa [hψ, map_add, map_mul, map_sum] using congrArg ψ hgen
  · simpa [hψ, map_mul] using congrArg ψ (hann i)

/-! ### Affine objects of the category -/

variable (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))

/-- The unit of the global-sections adjunction at a ring is the inverse of the canonical
isomorphism identifying the global sections of its spectrum with it. -/
public theorem toSpecΓ_eq_ΓSpecIso_inv (A : CommRingCat.{u}) :
    AlgebraicGeometry.toSpecΓ A = (Scheme.ΓSpecIso A).inv := by
  rw [Scheme.ΓSpecIso_inv]
  rfl

/-- The `k[s,t]`-algebra structure on `A` read off a morphism `Spec A ⟶ Spec k[s,t]`. -/
@[instance_reducible]
public def specAlgebra {A : Type u} [CommRing A]
    (τ : Spec (.of A) ⟶ Spec (.of (MvPolynomial (Fin 2) k))) :
    Algebra (MvPolynomial (Fin 2) k) A :=
  ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv ≫ τ.appTop ≫
    (Scheme.ΓSpecIso (.of A)).hom).hom.toAlgebra

/-- The algebra structure read off the spectrum of a ring map is the given one. -/
public theorem specAlgebra_specMap {A : Type u} [CommRing A]
    (φ : MvPolynomial (Fin 2) k →+* A) :
    @algebraMap (MvPolynomial (Fin 2) k) A _ _ (specAlgebra (Spec.map (CommRingCat.ofHom φ)))
      = φ := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have h' : (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv ≫
      (Spec.map (CommRingCat.ofHom φ)).appTop ≫ (Scheme.ΓSpecIso (.of A)).hom =
      CommRingCat.ofHom φ := by
    rw [h, Iso.inv_hom_id_assoc]
  exact congrArg CommRingCat.Hom.hom h'

/-- The one-member affine open cover of an affine scheme. -/
public def affineOpenCoverOfSpec (A : Type u) [CommRing A] :
    Scheme.AffineOpenCover.{u, u} (Spec (.of A)) where
  I₀ := PUnit.{u + 1}
  X := fun _ => .of A
  f := fun _ => 𝟙 _
  idx := fun _ => ⟨⟩
  covers := fun x => ⟨x, rfl⟩
  map_prop := fun _ => inferInstance

/-- An affine scheme over `Spec k[s,t]` whose ring is admissible is an object of the
category of Tag 07XR. -/
public theorem isArtinAxiomsObject_siteObject {A : Type u} [CommRing A]
    (hA : B.Contains (Spec (.of A)))
    (τ : Spec (.of A) ⟶ Spec (.of (MvPolynomial (Fin 2) k)))
    (h : @IsAdmissible k _ A _ (specAlgebra τ)) :
    IsArtinAxiomsObject k B hS (siteObject B _ hS hA τ) := by
  refine ⟨affineOpenCoverOfSpec A, fun i => ?_⟩
  refine isAdmissible_of_ringHom (specAlgebra τ) _ (Scheme.ΓSpecIso (.of A)).inv.hom ?_ h
  intro r
  have hmor : (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv ≫ τ.appTop ≫
      (Scheme.ΓSpecIso (.of A)).hom ≫ (Scheme.ΓSpecIso (.of A)).inv =
      AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k)) ≫ (𝟙 _ ≫ τ).appTop := by
    simp only [toSpecΓ_eq_ΓSpecIso_inv, Category.id_comp, Iso.hom_inv_id, Category.comp_id]
    rfl
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmor) r

/-- **The ring of an Artinian local object of the category is admissible.** If an object of
the category of Tag 07XR has an Artinian local coordinate ring, that ring is admissible: the
spectrum is a single point, so the member of the affine covering containing that point is the
whole spectrum. -/
public theorem isAdmissible_of_isArtinAxiomsObject {A : Type u} [CommRing A]
    [IsArtinianRing A] [IsLocalRing A]
    (T : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS)
    (hT : IsArtinAxiomsObject k B hS T)
    (e : (BigFppfOver.toScheme B _ hS).obj T ≅ Spec (.of A))
    (τ : Spec (.of A) ⟶ Spec (.of (MvPolynomial (Fin 2) k)))
    (hτ : B.inclusion.map T.hom = e.hom ≫ τ) :
    @IsAdmissible k _ A _ (specAlgebra τ) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hT
  have : Subsingleton (Spec (.of A) : Type u) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum A))
  obtain ⟨w, hw⟩ := 𝒰.covers (e.inv.base (IsLocalRing.closedPoint A))
  set i := 𝒰.idx (e.inv.base (IsLocalRing.closedPoint A)) with hi
  have hrange : Set.range (𝒰.f i ≫ e.hom) =
      Set.range (𝟙 (Spec (.of A)) : Spec (.of A) ⟶ Spec (.of A)) :=
    Set.eq_of_subset_of_subset (fun x _ => ⟨x, Subsingleton.elim _ _⟩)
      (fun x _ => ⟨w, Subsingleton.elim _ _⟩)
  let ε : Spec (𝒰.X i) ≅ Spec (.of A) :=
    IsOpenImmersion.isoOfRangeEq (𝒰.f i ≫ e.hom) (𝟙 _) hrange
  have hε : ε.hom = 𝒰.f i ≫ e.hom := by
    simpa using IsOpenImmersion.isoOfRangeEq_hom_fac (𝒰.f i ≫ e.hom) (𝟙 _) hrange
  refine isAdmissible_of_ringHom _ _ (ε.inv.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom).hom
    ?_ (h𝒰 i)
  intro r
  have hmor : ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv ≫
        (𝒰.f i ≫ B.inclusion.map T.hom).appTop) ≫
      (ε.inv.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom) =
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv ≫ τ.appTop ≫
        (Scheme.ΓSpecIso (.of A)).hom := by
    have hcomp : (𝒰.f i ≫ B.inclusion.map T.hom).appTop ≫ ε.inv.appTop = τ.appTop := by
      rw [← Scheme.Hom.comp_appTop]
      congr 1
      calc ε.inv ≫ 𝒰.f i ≫ B.inclusion.map T.hom
          = (ε.inv ≫ (𝒰.f i ≫ e.hom)) ≫ τ := by rw [hτ]; simp
        _ = τ := by rw [← hε, Iso.inv_hom_id, Category.id_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (Scheme.Hom.appTop (𝒰.f i ≫ B.inclusion.map T.hom)), hcomp]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmor) r

/-! ### The slice `s = 0` and its distinguished point -/

/-- The coordinate ring `k[s, t]/(s)` of the closed subscheme `s = 0`. -/
public abbrev sliceRing (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}

/-- The closed immersion `U = Spec k[s,t]/(s) ⟶ S = Spec k[s,t]`. -/
public abbrev sliceImmersion (k : Type u) [Field k] :
    Spec (.of (sliceRing k)) ⟶ Spec (.of (MvPolynomial (Fin 2) k)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)})))

/-- The slice `U ⟶ S` is a closed immersion. -/
public instance : IsClosedImmersion (sliceImmersion k) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The slice is of finite type over the base, hence lies on the chosen big fppf site. -/
public theorem contains_spec_sliceRing
    (hS' : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))) :
    B.Contains (Spec (.of (sliceRing k))) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (sliceImmersion k) hS'

/-- Evaluation of `k[s,t]/(s)` at the origin. -/
public def sliceEval : sliceRing k →+* k :=
  Ideal.Quotient.lift _ (MvPolynomial.eval (fun _ => (0 : k)))
    (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp)

/-- `sliceEval` evaluates the class of a polynomial at the origin. -/
@[simp] public theorem sliceEval_mk (g : MvPolynomial (Fin 2) k) :
    sliceEval (Ideal.Quotient.mk _ g) = MvPolynomial.eval (fun _ => (0 : k)) g :=
  rfl

/-- The point `u₀ = (s, t)` of the slice. -/
public def slicePoint (k : Type u) [Field k] : PrimeSpectrum (sliceRing k) :=
  ⟨RingHom.ker (sliceEval (k := k)),
    (RingHom.ker_isMaximal_of_surjective (sliceEval (k := k))
      (fun c => ⟨Ideal.Quotient.mk _ (MvPolynomial.C c), by simp⟩)).isPrime⟩

/-- The point `u₀` is closed: its ideal is maximal. -/
public theorem isMaximal_slicePoint : (slicePoint k).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (sliceEval (k := k))
    (fun c => ⟨Ideal.Quotient.mk _ (MvPolynomial.C c), by simp⟩)

/-- Both coordinates vanish at `u₀`. -/
public theorem mk_X_mem_slicePoint (j : Fin 2) :
    Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}) (X j) ∈
      (slicePoint k).asIdeal := by
  change sliceEval _ = 0
  simp

/-! ### The object of the category over the slice -/

/-- The structure functor of the category of Tag 07XR to schemes over `S = Spec k[s,t]`. -/
public abbrev artinAxiomsOver :
    artinAxiomsCategory k B hS ⥤ Over (Spec (.of (MvPolynomial (Fin 2) k))) :=
  ObjectProperty.ι (IsArtinAxiomsObject k B hS) ⋙ Over.post B.inclusion

/-- **The object `x` of `𝒳` over `U = Spec k[s,t]/(s)`.** Since `s = 0` on `U`, the slice
is itself an object of the category of Tag 07XR. -/
public def sliceObject : artinAxiomsCategory k B hS :=
  ⟨siteObject B _ hS (contains_spec_sliceRing B hS) (sliceImmersion k),
    isArtinAxiomsObject_siteObject B hS _ _
      (@isAdmissible_of_eq_zero k _ (sliceRing k) _ (specAlgebra (sliceImmersion k)) (by
        rw [specAlgebra_specMap]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)))⟩

/-- The underlying scheme of `sliceObject` is the slice `U = Spec k[s,t]/(s)`. -/
public theorem sliceObject_left :
    ((artinAxiomsOver B hS).obj (sliceObject B hS)).left = Spec (.of (sliceRing k)) := by
  delta sliceObject
  rfl


private theorem germ_eq_zero_iff
    {R R' : CommRingCat.{u}} (m : R ⟶ R') (p : ↥(Spec R')) (r : ↥R) :
    (Scheme.stalkClosedPointTo ((Spec R').fromSpecResidueField p ≫ Spec.map m)).hom
        ((Spec R).presheaf.germ ⊤
          (((Spec R').fromSpecResidueField p ≫ Spec.map m).base
            (IsLocalRing.closedPoint ↥((Spec R').residueField p))) trivial
          ((Scheme.ΓSpecIso R).inv.hom r)) = 0 ↔ m.hom r ∈ p.asIdeal := by
  have : p.asIdeal.IsPrime := p.2
  set g := (Spec R').fromSpecResidueField p ≫ Spec.map m with hgdef
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk g
  rw [Spec.fromSpecStalk_eq, ← Spec.map_comp] at h1
  have h2 : Spec.map (m ≫ CommRingCat.ofHom (algebraMap ↥R' p.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R' p).inv) = g := by
    rw [Spec.map_comp, Spec.map_comp, hgdef,
      ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  have h3 := Spec.map_inj.mp (h1.trans h2.symm)
  have h4 := congrArg (fun (t : R ⟶ (Spec R').residueField p) => t.hom r) h3
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h4
  rw [h4, show ∀ x, (Scheme.Spec.residueFieldIso R' p).inv.hom x = 0 ↔ x = 0 from fun x =>
    map_eq_zero_iff _ ((Scheme.Spec.residueFieldIso R' p).inv.hom.injective)]
  exact Ideal.algebraMap_residueField_eq_zero



variable {k : Type u} [Field k]

/-! ### The algebra structure read off the local ring at a point of the base -/

/-- The structure morphism of an algebra over the local ring of `Spec k[s,t]` at `p` is the
spectrum of a map out of `k[s,t]`, namely of the germ at `p` followed by the algebra map. -/
private theorem fromSpecStalk_comp_eq_spec_map
    (p : ↥(Spec (.of (MvPolynomial (Fin 2) k)))) {C : Type u} [CommRing C]
    (inst : Algebra ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) C) :
    Spec.map (CommRingCat.ofHom (@algebraMap _ C _ _ inst)) ≫
        (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk p =
      Spec.map (CommRingCat.ofHom
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv ≫
          (Spec (.of (MvPolynomial (Fin 2) k))).presheaf.germ ⊤ p trivial ≫
          CommRingCat.ofHom (@algebraMap _ C _ _ inst)).hom) := by
  rw [Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rfl

/-- That algebra structure sends `r` to the image of its germ at `p`. -/
private theorem algebraMap_specAlgebra_apply
    (p : ↥(Spec (.of (MvPolynomial (Fin 2) k)))) {C : Type u} [CommRing C]
    (inst : Algebra ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) C)
    (r : MvPolynomial (Fin 2) k) :
    @algebraMap (MvPolynomial (Fin 2) k) C _ _
        (specAlgebra (Spec.map (CommRingCat.ofHom (@algebraMap _ C _ _ inst)) ≫
          (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk p)) r =
      @algebraMap _ C _ _ inst
        (((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.germ ⊤ p trivial).hom
          ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom r)) := by
  rw [fromSpecStalk_comp_eq_spec_map, specAlgebra_specMap]
  rfl

/-- The structure morphism is the spectrum of the algebra structure it induces. -/
private theorem spec_map_algebraMap_specAlgebra
    (p : ↥(Spec (.of (MvPolynomial (Fin 2) k)))) {C : Type u} [CommRing C]
    (inst : Algebra ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) C) :
    Spec.map (CommRingCat.ofHom (@algebraMap (MvPolynomial (Fin 2) k) C _ _
        (specAlgebra (Spec.map (CommRingCat.ofHom (@algebraMap _ C _ _ inst)) ≫
          (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk p)))) =
      Spec.map (CommRingCat.ofHom (@algebraMap _ C _ _ inst)) ≫
        (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk p := by
  rw [fromSpecStalk_comp_eq_spec_map, specAlgebra_specMap]

/-! ### The coordinates vanish at the origin of the slice -/

/-- Both coordinates `s` and `t` die in the residue field of the slice at its origin. -/
private theorem algebraMap_residueField_germ_X_eq_zero (j : Fin 2) :
    @algebraMap _ ↥((Over.mk (sliceImmersion k)).left.residueField (slicePoint k)) _ _
        (residueFieldAlgebra (Over.mk (sliceImmersion k)) (slicePoint k))
      (((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.germ ⊤
          (basePoint (Over.mk (sliceImmersion k)) (slicePoint k)) trivial).hom
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom (X j))) = 0 :=
  germ_eq_zero_iff (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}))) (slicePoint k) (X j)
    |>.mpr (mk_X_mem_slicePoint j)

/-- In an Artinian local algebra over the local ring at `p` with the given residue field, an
element of `k[s,t]` dying in that residue field lands in the maximal ideal. -/
private theorem algebraMap_specAlgebra_mem_maximalIdeal
    {p : ↥(Spec (.of (MvPolynomial (Fin 2) k)))} {κ : Type u} {instF : Field κ}
    {instA : Algebra ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) κ}
    (C : @ArtinianLocalAlgCat.{u, u, u}
      ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) κ _ instF instA)
    (r : MvPolynomial (Fin 2) k)
    (h : @algebraMap _ κ _ _ instA
        (((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.germ ⊤ p trivial).hom
          ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom r)) = 0) :
    @algebraMap (MvPolynomial (Fin 2) k) ↥C _ _
        (specAlgebra (Spec.map (CommRingCat.ofHom
            (algebraMap ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) ↥C)) ≫
          (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk p)) r ∈
      IsLocalRing.maximalIdeal ↥C := by
  rw [algebraMap_specAlgebra_apply, ← IsLocalRing.residue_eq_zero_iff]
  refine C.residueEquiv.injective ?_
  rw [map_zero, show IsLocalRing.residue ↥C (@algebraMap _ ↥C _ _ C.algebra _) =
      @algebraMap _ (IsLocalRing.ResidueField ↥C) _ _ _
        (((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.germ ⊤ p trivial).hom
          ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom r)) from by
    rw [IsScalarTower.algebraMap_apply
      ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) ↥C
      (IsLocalRing.ResidueField ↥C)]
    simp [IsLocalRing.ResidueField.algebraMap_eq]]
  exact (C.residueEquiv.commutes _).trans h

/-! ### Factoring through the slice -/

/-- An algebra over the local ring at `p` in which `s` vanishes receives a morphism to the
slice, compatibly with the structure morphisms to `Spec k[s,t]`. -/
private theorem exists_comp_sliceImmersion
    (p : ↥(Spec (.of (MvPolynomial (Fin 2) k)))) {C : Type u} [CommRing C]
    (inst : Algebra ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) C)
    (h : @algebraMap (MvPolynomial (Fin 2) k) C _ _
        (specAlgebra (Spec.map (CommRingCat.ofHom (@algebraMap _ C _ _ inst)) ≫
          (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk p)) (X 0) = 0) :
    ∃ β : Spec (.of C) ⟶ Spec (.of (sliceRing k)),
      β ≫ sliceImmersion k =
        Spec.map (CommRingCat.ofHom (@algebraMap _ C _ _ inst)) ≫
          (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk p := by
  have hker : ∀ w ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) k)},
      @algebraMap (MvPolynomial (Fin 2) k) C _ _
        (specAlgebra (Spec.map (CommRingCat.ofHom (@algebraMap _ C _ _ inst)) ≫
          (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk p)) w = 0 := by
    intro w hw
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    rw [map_mul, h, mul_zero]
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ _ hker)), ?_⟩
  refine Eq.trans ?_ (spec_map_algebraMap_specAlgebra p inst)
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ _ hker)) ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}))) = _
  rw [← Spec.map_comp]
  exact Spec.map_inj.mpr (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

/-! ### Versality of the slice at the origin -/

/-- An arrow into the slice object lies over the slice immersion. -/
private theorem hom_left_comp_sliceImmersion (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))
    {y : artinAxiomsCategory k B hS} (b : y ⟶ sliceObject B hS) :
    (b.hom.left).hom ≫ sliceImmersion k = y.obj.hom.hom := by
  change (b.hom.left ≫ (sliceObject B hS).obj.hom).hom = _
  rw [Over.w b.hom]

/-- Arrows into the slice object are unique: its structure morphism is a closed immersion,
hence a monomorphism, and the site inclusion is faithful. -/
private theorem hom_sliceObject_eq (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))
    {y : artinAxiomsCategory k B hS} (b₁ b₂ : y ⟶ sliceObject B hS) : b₁ = b₂ := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact (cancel_mono (sliceImmersion k)).mp
    ((hom_left_comp_sliceImmersion B hS b₁).trans (hom_left_comp_sliceImmersion B hS b₂).symm)

/-- **The slice is versal at the origin.** -/
@[stacks 07XR "the object x over U = Spec(k[s,t]/(s)) is versal at u_0 = (s,t)"]
public theorem isVersalAt_sliceObject (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))) :
    IsVersalAt (Over.mk (sliceImmersion k)) (artinAxiomsOver B hS) (slicePoint k)
      (sliceObject B hS) (by delta sliceObject; rfl) := by
  intro A C f _ y z _ hz i _ a _
  have hw := Over.w (eqToHom hz)
  rw [Over.eqToHom_left] at hw
  have hadm := isAdmissible_of_isArtinAxiomsObject (A := ↥C) B hS z.1 z.2
    (eqToIso (congrArg Over.left hz)) _ hw.symm
  have hs0 := @eq_zero_of_isAdmissible k _ ↥C _ _ (specAlgebra _)
    (algebraMap_specAlgebra_mem_maximalIdeal C (X 0) (algebraMap_residueField_germ_X_eq_zero 0))
    (algebraMap_specAlgebra_mem_maximalIdeal C (X 1) (algebraMap_residueField_germ_X_eq_zero 1))
    hadm
  obtain ⟨β, hβ⟩ := exists_comp_sliceImmersion _ _ hs0
  have hcond : (ObjectProperty.homMk (eqToHom (congrArg Over.left hz) ≫ β) :
      z.obj.left ⟶ (sliceObject B hS).obj.left) ≫ (sliceObject B hS).obj.hom =
      z.obj.hom := by
    apply ObjectProperty.hom_ext
    change (eqToHom (congrArg Over.left hz) ≫ β) ≫ sliceImmersion k = _
    rwa [Category.assoc, hβ]
  exact ⟨ObjectProperty.homMk (Over.homMk _ hcond), hom_sliceObject_eq B hS _ _⟩

/-! ### Square-zero extensions with a twisted algebra structure -/

section TwistedSquareZero

variable {Λ : Type u} [CommRing Λ] {κ : Type u} [Field κ] [Algebra Λ κ]
  (M : ModuleCat.{u} κ) [Module.Finite κ ↥M]
  (instD : Algebra Λ (TrivSqZeroExt κ ↥M))
  (hinst : ∀ o : Λ, (@algebraMap Λ (TrivSqZeroExt κ ↥M) _ _ instD o).fst = algebraMap Λ κ o)

/-- **The square-zero extension `k[M]` as an object of `𝒞_Λ` for a twisted base structure.**
The `Λ`-algebra structure is an arbitrary one lifting the structure map of `κ`, not
necessarily the split one of `Deformation.Artin.squareZeroArtinianObj`. -/
private def twistedSquareZeroObj : ArtinianLocalAlgCat.{u, u, u} Λ κ where
  carrier := TrivSqZeroExt κ ↥M
  algebra := instD
  isArtinianRing := isArtinianRing_trivSqZeroExt κ M
  isLocalRing := isLocalRing_trivSqZeroExt κ M
  residueEquiv :=
    letI : IsLocalRing (TrivSqZeroExt κ ↥M) := isLocalRing_trivSqZeroExt κ M
    letI : Algebra Λ (TrivSqZeroExt κ ↥M) := instD
    Deformation.residueEquivOfAugmentation
      ({ toRingHom := (TrivSqZeroExt.fstHom κ κ ↥M).toRingHom,
         commutes' := hinst } : TrivSqZeroExt κ ↥M →ₐ[Λ] κ)
      TrivSqZeroExt.fst_surjective

private theorem algebraMap_twistedSquareZeroObj :
    @algebraMap Λ ↥(twistedSquareZeroObj M instD hinst) _ _ _ =
      @algebraMap Λ (TrivSqZeroExt κ ↥M) _ _ instD := rfl

/-- The augmentation of the twisted square-zero extension onto the residue field. -/
private def twistedSquareZeroProjection :
    twistedSquareZeroObj M instD hinst ⟶ fieldArtinianObj Λ κ where
  hom :=
    { toRingHom := (TrivSqZeroExt.fstHom κ κ ↥M).toRingHom
      commutes' := hinst }
  isLocal := ⟨fun _ ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  residue_comm _ := rfl

private theorem surjective_twistedSquareZeroProjection :
    Function.Surjective (twistedSquareZeroProjection M instD hinst).hom :=
  TrivSqZeroExt.fst_surjective

private theorem hom_twistedSquareZeroProjection :
    (twistedSquareZeroProjection M instD hinst).hom.toRingHom =
      (TrivSqZeroExt.fstHom κ κ ↥M).toRingHom := rfl

end TwistedSquareZero
/-! ### The residue field of the slice at a point -/

section Nonversal

variable {k : Type u} [Field k] (u : ↥(Spec (.of (sliceRing k))))

/-- The image in `Spec k[s,t]` of the residue-field point of the slice at `u`. -/
private abbrev sliceBasePrime : ↥(Spec (.of (MvPolynomial (Fin 2) k))) :=
  basePoint (Over.mk (sliceImmersion k)) u

/-- The residue field of the slice at `u`. -/
private abbrev sliceKappa : Type u := ↥((Over.mk (sliceImmersion k)).left.residueField u)

/-- The residue field of the slice at `u`, as a module over itself. -/
private def sliceModule : ModuleCat.{u} (sliceKappa u) :=
  ModuleCat.of (sliceKappa u) (sliceKappa u)

private instance : Module.Finite (sliceKappa u) ↥(sliceModule u) :=
  inferInstanceAs (Module.Finite (sliceKappa u) (sliceKappa u))

/-- The nilpotent generator `ε` of the dual numbers at `u`. -/
private def sliceEps : ↥(sliceModule u) := (1 : sliceKappa u)

private theorem sliceEps_ne_zero : sliceEps u ≠ 0 :=
  (one_ne_zero : (1 : sliceKappa u) ≠ 0)

/-- The dual numbers over the residue field of the slice at `u`. -/
private abbrev sliceDual : Type u := TrivSqZeroExt (sliceKappa u) ↥(sliceModule u)

/-- The structure map `k[s,t] → κ(u)` of the residue field of the slice at `u`. -/
private def sliceResidueMap : MvPolynomial (Fin 2) k →+* sliceKappa u :=
  ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv ≫
    (Spec (.of (MvPolynomial (Fin 2) k))).presheaf.germ ⊤
      (sliceBasePrime u) trivial ≫
    CommRingCat.ofHom (@algebraMap _ _ _ _
      (residueFieldAlgebra (Over.mk (sliceImmersion k)) u))).hom

private theorem sliceResidueMap_eq_zero_iff (r : MvPolynomial (Fin 2) k) :
    sliceResidueMap u r = 0 ↔
      Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}) r ∈
        (u : PrimeSpectrum (sliceRing k)).asIdeal :=
  germ_eq_zero_iff (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}))) u r

private theorem sliceResidueMap_X_zero : sliceResidueMap u (X 0) = 0 := by
  rw [sliceResidueMap_eq_zero_iff, Ideal.Quotient.mk_singleton_self]
  exact Submodule.zero_mem _

/-- The map `k[s,t] → κ(u)[ε]` sending `s` to `ε` and `t` to its residue. -/
private def sliceDualMap : MvPolynomial (Fin 2) k →+* sliceDual u :=
  MvPolynomial.eval₂Hom
    ((TrivSqZeroExt.inlHom (sliceKappa u) ↥(sliceModule u)).comp
      ((sliceResidueMap u).comp MvPolynomial.C))
    (fun j => if j = 0 then TrivSqZeroExt.inr (sliceEps u)
      else TrivSqZeroExt.inl (sliceResidueMap u (X 1)))

private theorem sliceDualMap_C (c : k) :
    sliceDualMap u (MvPolynomial.C c) =
      TrivSqZeroExt.inl (sliceResidueMap u (MvPolynomial.C c)) := by
  change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c) = _
  rw [MvPolynomial.eval₂Hom_C]
  rfl

private theorem sliceDualMap_X_zero :
    sliceDualMap u (X 0) = TrivSqZeroExt.inr (sliceEps u) := by
  change MvPolynomial.eval₂Hom _ _ (X 0) = _
  rw [MvPolynomial.eval₂Hom_X']
  simp

private theorem sliceDualMap_X_one :
    sliceDualMap u (X 1) = TrivSqZeroExt.inl (sliceResidueMap u (X 1)) := by
  change MvPolynomial.eval₂Hom _ _ (X 1) = _
  rw [MvPolynomial.eval₂Hom_X']
  simp

private theorem fst_sliceDualMap (r : MvPolynomial (Fin 2) k) :
    (sliceDualMap u r).fst = sliceResidueMap u r := by
  have h : (TrivSqZeroExt.fstHom (sliceKappa u) (sliceKappa u)
        ↥(sliceModule u)).toRingHom.comp (sliceDualMap u) = sliceResidueMap u := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · change (sliceDualMap u (MvPolynomial.C c)).fst = sliceResidueMap u (MvPolynomial.C c)
      rw [sliceDualMap_C, TrivSqZeroExt.fst_inl]
    · fin_cases j
      · change (sliceDualMap u (X 0)).fst = sliceResidueMap u (X 0)
        rw [sliceDualMap_X_zero, sliceResidueMap_X_zero, TrivSqZeroExt.fst_inr]
      · change (sliceDualMap u (X 1)).fst = sliceResidueMap u (X 1)
        rw [sliceDualMap_X_one, TrivSqZeroExt.fst_inl]
  exact DFunLike.congr_fun h r

private theorem sliceResidueMap_X_one_ne_zero
    (hu : Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}) (X 1) ∉
      (u : PrimeSpectrum (sliceRing k)).asIdeal) :
    sliceResidueMap u (X 1) ≠ 0 := fun h => hu ((sliceResidueMap_eq_zero_iff u (X 1)).mp h)

/-! ### Lifting the structure map to the local ring of the base -/

/-- The stalk of `Spec k[s,t]` at a point is the localization of `k[s,t]` there. -/
private instance (p : ↥(Spec (.of (MvPolynomial (Fin 2) k)))) :
    Algebra (MvPolynomial (Fin 2) k) ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p) :=
  StructureSheaf.stalkAlgebra (MvPolynomial (Fin 2) k) p

private instance (p : ↥(Spec (.of (MvPolynomial (Fin 2) k)))) :
    IsLocalization.AtPrime ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk p)
      p.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk (MvPolynomial (Fin 2) k) p

/-- The elements of `k[s,t]` not vanishing at the image point become units in the dual
numbers. -/
private theorem isUnit_sliceDualMap (y : MvPolynomial (Fin 2) k)
    (hy : y ∈ (sliceBasePrime u).asIdeal.primeCompl) : IsUnit (sliceDualMap u y) := by
  refine TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ?_
  rw [fst_sliceDualMap,
    show sliceResidueMap u y = @algebraMap _ (sliceKappa u) _ _
      (residueFieldAlgebra (Over.mk (sliceImmersion k)) u)
        (algebraMap _ _ y) from rfl]
  exact RingHom.isUnit_map _
    ((IsLocalization.AtPrime.isUnit_to_map_iff _ (sliceBasePrime u).asIdeal y).mpr hy)

/-- **The `k[s,t]`-algebra structure on the dual numbers extends to the local ring of the
base**, because `t` and every other element not vanishing at the point become units. -/
private def sliceDualLift :
    ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk (sliceBasePrime u)) →+*
      sliceDual u :=
  IsLocalization.lift (M := (sliceBasePrime u).asIdeal.primeCompl) (g := sliceDualMap u)
    (fun y => isUnit_sliceDualMap u y y.2)

private theorem sliceDualLift_germ (r : MvPolynomial (Fin 2) k) :
    sliceDualLift u
        (((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.germ ⊤ (sliceBasePrime u) trivial).hom
          ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom r)) =
      sliceDualMap u r := by
  exact IsLocalization.lift_eq (fun y => isUnit_sliceDualMap u y y.2) r

/-- The lift reduces to the structure map of the residue field. -/
private theorem fst_sliceDualLift
    (o : ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk (sliceBasePrime u))) :
    (sliceDualLift u o).fst = @algebraMap _ (sliceKappa u) _ _
      (residueFieldAlgebra (Over.mk (sliceImmersion k)) u) o := by
  have h : (TrivSqZeroExt.fstHom (sliceKappa u) (sliceKappa u)
        ↥(sliceModule u)).toRingHom.comp (sliceDualLift u) =
      (@algebraMap _ (sliceKappa u) _ _
        (residueFieldAlgebra (Over.mk (sliceImmersion k)) u) : _ →+* _) := by
    refine IsLocalization.ringHom_ext (sliceBasePrime u).asIdeal.primeCompl
      (RingHom.ext fun r => ?_)
    change (sliceDualLift u
        (((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.germ ⊤ (sliceBasePrime u) trivial).hom
          ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) k))).inv.hom r))).fst =
      sliceResidueMap u r
    rw [sliceDualLift_germ, fst_sliceDualMap]
  exact DFunLike.congr_fun h o

/-! ### The two objects of the lifting problem -/

/-- The residue field at `u`, as an object of `𝒞_𝒪`. -/
private abbrev sliceFieldObj : @ArtinianLocalAlgCat.{u, u, u}
    ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk (sliceBasePrime u))
    (sliceKappa u) _ _ (residueFieldAlgebra (Over.mk (sliceImmersion k)) u) :=
  @fieldArtinianObj _ (sliceKappa u) _ _ (residueFieldAlgebra (Over.mk (sliceImmersion k)) u)

/-- The dual numbers at `u` with `s` sent to `ε`, as an object of `𝒞_𝒪`. -/
private abbrev sliceDualObj : @ArtinianLocalAlgCat.{u, u, u}
    ↥((Spec (.of (MvPolynomial (Fin 2) k))).presheaf.stalk (sliceBasePrime u))
    (sliceKappa u) _ _ (residueFieldAlgebra (Over.mk (sliceImmersion k)) u) :=
  @twistedSquareZeroObj _ _ (sliceKappa u) _
    (residueFieldAlgebra (Over.mk (sliceImmersion k)) u) (sliceModule u) _
    (sliceDualLift u).toAlgebra (fst_sliceDualLift u)

/-- The structure morphism of `Spec κ(u)` over `Spec k[s,t]`, through the local ring. -/
private abbrev sliceFieldStruct :
    Spec (.of (sliceKappa u)) ⟶ Spec (.of (MvPolynomial (Fin 2) k)) :=
  Spec.map (CommRingCat.ofHom (@algebraMap _ (sliceKappa u) _ _
      (residueFieldAlgebra (Over.mk (sliceImmersion k)) u))) ≫
    (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk (sliceBasePrime u)

/-- The structure morphism of `Spec κ(u)[ε]` over `Spec k[s,t]`, through the local ring. -/
private abbrev sliceDualStruct :
    Spec (.of (sliceDual u)) ⟶ Spec (.of (MvPolynomial (Fin 2) k)) :=
  Spec.map (CommRingCat.ofHom (sliceDualLift u)) ≫
    (Spec (.of (MvPolynomial (Fin 2) k))).fromSpecStalk (sliceBasePrime u)

private theorem algebraMap_specAlgebra_sliceFieldStruct :
    @algebraMap (MvPolynomial (Fin 2) k) (sliceKappa u) _ _
        (specAlgebra (sliceFieldStruct u)) = sliceResidueMap u :=
  RingHom.ext fun r => algebraMap_specAlgebra_apply (sliceBasePrime u) _ r

private theorem algebraMap_specAlgebra_sliceDualStruct :
    @algebraMap (MvPolynomial (Fin 2) k) (sliceDual u) _ _
        (specAlgebra (sliceDualStruct u)) = sliceDualMap u :=
  RingHom.ext fun r =>
    (algebraMap_specAlgebra_apply (sliceBasePrime u) (sliceDualLift u).toAlgebra r).trans
      (sliceDualLift_germ u r)

/-- `Spec κ(u)` lies on the site, being the residue-field point of the slice. -/
private theorem contains_spec_sliceKappa (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))) :
    B.Contains (Spec (.of (sliceKappa u))) :=
  Scheme.size_lt_of_mono_quasiCompact
    ((Over.mk (sliceImmersion k)).left.fromSpecResidueField u) (contains_spec_sliceRing B hS)

/-- `Spec κ(u)[ε]` lies on the site: its ring has the cardinality of `κ(u)`. -/
private theorem contains_spec_sliceDual (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))) :
    B.Contains (Spec (.of (sliceDual u))) := by
  refine Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (.of (sliceDual u)) (contains_spec_sliceKappa u B hS) ?_
  refine le_trans ?_ (Cardinal.self_le_power _ Cardinal.one_le_aleph0)
  rw [Scheme.size_Spec]
  calc Cardinal.mk ↥(CommRingCat.of (sliceDual u))
      = Cardinal.mk (sliceKappa u × sliceKappa u) :=
        Cardinal.mk_congr (Equiv.refl (sliceKappa u × sliceKappa u) :
          ↥(CommRingCat.of (sliceDual u)) ≃ sliceKappa u × sliceKappa u)
    _ = Cardinal.mk (sliceKappa u) * Cardinal.mk (sliceKappa u) := by
        simp [Cardinal.mk_prod]
    _ ≤ max (max (Cardinal.mk (sliceKappa u)) (Cardinal.mk (sliceKappa u))) Cardinal.aleph0 :=
        Cardinal.mul_le_max _ _
    _ = max Cardinal.aleph0 (Cardinal.mk ↥(CommRingCat.of (sliceKappa u))) := by
        simp [max_comm]

/-! ### The lifting problem with no solution -/

private theorem isUnit_sliceDualMap_X_one
    (hu : Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}) (X 1) ∉
      (u : PrimeSpectrum (sliceRing k)).asIdeal) :
    IsUnit (sliceDualMap u (X 1)) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (by
    rw [fst_sliceDualMap]
    exact isUnit_iff_ne_zero.mpr (sliceResidueMap_X_one_ne_zero u hu))

/-- The residue field at `u` is admissible: `s` vanishes on it. -/
private theorem isAdmissible_sliceKappa :
    @IsAdmissible k _ (sliceKappa u) _ (specAlgebra (sliceFieldStruct u)) :=
  @isAdmissible_of_eq_zero k _ (sliceKappa u) _ (specAlgebra (sliceFieldStruct u))
    (by rw [algebraMap_specAlgebra_sliceFieldStruct]; exact sliceResidueMap_X_zero u)

/-- The dual numbers at `u` are admissible: `t` is a unit there, so `s`, `t` already
generate the unit ideal with no further generators. -/
private theorem isAdmissible_sliceDual
    (hu : Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}) (X 1) ∉
      (u : PrimeSpectrum (sliceRing k)).asIdeal) :
    @IsAdmissible k _ (sliceDual u) _ (specAlgebra (sliceDualStruct u)) := by
  obtain ⟨v, hv⟩ := isUnit_sliceDualMap_X_one u hu
  refine ⟨0, fun i => i.elim0, 0, ↑v⁻¹, fun i => i.elim0, ?_, fun i => i.elim0⟩
  rw [algebraMap_specAlgebra_sliceDualStruct]
  simp [← hv]

/-- The structure morphism of `Spec κ(u)` is the residue-field point of the slice followed
by the slice immersion. -/
private theorem sliceFieldStruct_eq :
    sliceFieldStruct u =
      (Over.mk (sliceImmersion k)).left.fromSpecResidueField u ≫ sliceImmersion k :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk
    ((Over.mk (sliceImmersion k)).left.fromSpecResidueField u ≫ sliceImmersion k)

/-- The augmentation of the dual numbers is a morphism over `Spec k[s,t]`. -/
private theorem spec_map_fst_comp_sliceDualStruct :
    Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.fstHom (sliceKappa u) (sliceKappa u) ↥(sliceModule u)).toRingHom) ≫
      sliceDualStruct u = sliceFieldStruct u := by
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (sliceDualLift u)) ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map _ ≫ _ = Spec.map _ ≫ _
  congr 1
  exact Spec.map_inj.mpr (CommRingCat.hom_ext (RingHom.ext (fst_sliceDualLift u)))

/-- **The slice is not versal at any point where `t` does not vanish.** The lifting problem
along `κ(u)[ε] → κ(u)`, with `s` acting as `ε`, has no solution: a solution would factor the
structure morphism of `κ(u)[ε]` through the slice, forcing `s = 0` there. -/
private theorem not_isVersalAt_of_mk_X_one_notMem (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))
    (hu : Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}) (X 1) ∉
      (u : PrimeSpectrum (sliceRing k)).asIdeal) :
    ¬ IsVersalAt (Over.mk (sliceImmersion k)) (artinAxiomsOver B hS) u
      (sliceObject B hS) (by delta sliceObject; rfl) := by
  intro hv
  have hyobj : IsArtinAxiomsObject k B hS
      (siteObject B _ hS (contains_spec_sliceKappa u B hS) (sliceFieldStruct u)) :=
    isArtinAxiomsObject_siteObject B hS _ _ (isAdmissible_sliceKappa u)
  have hzobj : IsArtinAxiomsObject k B hS
      (siteObject B _ hS (contains_spec_sliceDual u B hS) (sliceDualStruct u)) :=
    isArtinAxiomsObject_siteObject B hS _ _ (isAdmissible_sliceDual u hu)
  obtain ⟨b, -⟩ := hv (sliceFieldObj u) (sliceDualObj u)
    (@twistedSquareZeroProjection _ _ (sliceKappa u) _
      (residueFieldAlgebra (Over.mk (sliceImmersion k)) u) (sliceModule u) _
      (sliceDualLift u).toAlgebra (fst_sliceDualLift u))
    (@surjective_twistedSquareZeroProjection _ _ (sliceKappa u) _
      (residueFieldAlgebra (Over.mk (sliceImmersion k)) u) (sliceModule u) _
      (sliceDualLift u).toAlgebra (fst_sliceDualLift u))
    ⟨_, hyobj⟩ ⟨_, hzobj⟩ rfl rfl
    (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom
        (TrivSqZeroExt.fstHom (sliceKappa u) (sliceKappa u) ↥(sliceModule u)).toRingHom)))
      (ObjectProperty.hom_ext _ (spec_map_fst_comp_sliceDualStruct u))))
    (by
      change (𝟙 _ : _ ⟶ _) ≫ Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.fstHom (sliceKappa u) (sliceKappa u) ↥(sliceModule u)).toRingHom) ≫
          (𝟙 _ : _ ⟶ _) = _
      simp
      rfl)
    (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
      ((Over.mk (sliceImmersion k)).left.fromSpecResidueField u))
      (ObjectProperty.hom_ext _ (sliceFieldStruct_eq u).symm)))
    (by
      change Spec.map (CommRingCat.ofHom (@residueMap _ (sliceKappa u) _ _
            (residueFieldAlgebra (Over.mk (sliceImmersion k)) u) (sliceFieldObj u))) ≫
          (𝟙 _ : _ ⟶ _) ≫
          (Over.mk (sliceImmersion k)).left.fromSpecResidueField u ≫ (𝟙 _ : _ ⟶ _) = _
      have hid : CommRingCat.ofHom (@residueMap _ (sliceKappa u) _ _
          (residueFieldAlgebra (Over.mk (sliceImmersion k)) u) (sliceFieldObj u)) =
            𝟙 (CommRingCat.of (sliceKappa u)) :=
        CommRingCat.hom_ext (@residueMap_fieldArtinianObj _ (sliceKappa u) _ _
          (residueFieldAlgebra (Over.mk (sliceImmersion k)) u))
      rw [hid]
      change Spec.map (𝟙 (CommRingCat.of (sliceKappa u))) ≫ (𝟙 _ : _ ⟶ _) ≫
          (Over.mk (sliceImmersion k)).left.fromSpecResidueField u ≫ (𝟙 _ : _ ⟶ _) = _
      rw [Spec.map_id]
      simp)
  have hwb : (b.hom.left).hom ≫ sliceImmersion k = sliceDualStruct u :=
    hom_left_comp_sliceImmersion B hS b
  obtain ⟨γ, hγ⟩ : ∃ γ, Spec.map γ = (b.hom.left).hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  rw [← hγ] at hwb
  have h2 : Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)})) ≫ γ) =
      Spec.map (CommRingCat.ofHom (sliceDualMap u)) := by
    rw [Spec.map_comp]
    refine hwb.trans ?_
    calc sliceDualStruct u
        = Spec.map (CommRingCat.ofHom (@algebraMap _ (sliceDual u) _ _
            (specAlgebra (sliceDualStruct u)))) :=
          (spec_map_algebraMap_specAlgebra (sliceBasePrime u)
            (sliceDualLift u).toAlgebra).symm
      _ = Spec.map (CommRingCat.ofHom (sliceDualMap u)) := by
          rw [algebraMap_specAlgebra_sliceDualStruct]
  have h3 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_inj.mp h2)) (X 0)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
    Function.comp_apply] at h3
  rw [sliceDualMap_X_zero, Ideal.Quotient.mk_singleton_self, map_zero] at h3
  exact sliceEps_ne_zero u (by simpa using congrArg TrivSqZeroExt.snd h3.symm)

/-! ### The origin is the only point of the slice at which `t` vanishes -/

private theorem mk_X_one_ne_zero :
    Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}) (X 1) ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have h1 := congrArg (MvPolynomial.eval (fun j : Fin 2 => if j = 0 then (0 : k) else 1)) hc
  simp at h1

private theorem eq_slicePoint_of_mk_X_one_mem (u : ↥(Spec (.of (sliceRing k))))
    (hu : Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}) (X 1) ∈
      (u : PrimeSpectrum (sliceRing k)).asIdeal) :
    (u : PrimeSpectrum (sliceRing k)) = slicePoint k := by
  have key : ∀ G : MvPolynomial (Fin 2) k,
      Ideal.Quotient.mk (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)})
          (G - MvPolynomial.C (MvPolynomial.eval (fun _ => (0 : k)) G)) ∈
        (u : PrimeSpectrum (sliceRing k)).asIdeal := by
    intro G
    induction G using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq =>
        have h : (p + q) - MvPolynomial.C (MvPolynomial.eval (fun _ => (0 : k)) (p + q)) =
            (p - MvPolynomial.C (MvPolynomial.eval (fun _ => (0 : k)) p)) +
              (q - MvPolynomial.C (MvPolynomial.eval (fun _ => (0 : k)) q)) := by
          rw [map_add, map_add]; ring
        rw [h, map_add]
        exact Submodule.add_mem _ hp hq
    | mul_X p i _ =>
        have h : p * X i -
            MvPolynomial.C (MvPolynomial.eval (fun _ => (0 : k)) (p * X i)) = p * X i := by
          simp
        rw [h, map_mul]
        refine Ideal.mul_mem_left _ _ ?_
        fin_cases i
        · rw [show (X ⟨0, by omega⟩ : MvPolynomial (Fin 2) k) = X 0 from rfl,
            Ideal.Quotient.mk_singleton_self]
          exact Submodule.zero_mem _
        · exact hu
  have hle : (slicePoint k).asIdeal ≤ (u : PrimeSpectrum (sliceRing k)).asIdeal := by
    intro g hg
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective g
    have h0 : MvPolynomial.eval (fun _ => (0 : k)) G = 0 := by
      simpa using RingHom.mem_ker.mp hg
    have h1 := key G
    rwa [map_sub, h0, map_zero, map_zero, sub_zero] at h1
  exact PrimeSpectrum.ext ((isMaximal_slicePoint (k := k)).eq_of_le
    (u : PrimeSpectrum (sliceRing k)).2.ne_top hle).symm

/-- **The slice is versal at no point other than the origin.** -/
@[stacks 07XR "x is versal at no other point of U"]
public theorem not_isVersalAt_sliceObject (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))
    (hu : (u : PrimeSpectrum (sliceRing k)) ≠ slicePoint k) :
    ¬ IsVersalAt (Over.mk (sliceImmersion k)) (artinAxiomsOver B hS) u
      (sliceObject B hS) (by delta sliceObject; rfl) :=
  not_isVersalAt_of_mk_X_one_notMem u B hS
    (fun hmem => hu (eq_slicePoint_of_mk_X_one_mem u hmem))

/-- Every open neighbourhood of the origin of the slice contains a closed point other than
the origin: the slice is a Jacobson scheme and its generic point lies in the
neighbourhood. -/
private theorem exists_isClosed_singleton_mem_ne_slicePoint
    (V : Set ↥(Spec (.of (sliceRing k)))) (hV : IsOpen V) (hu₀ : slicePoint k ∈ V) :
    ∃ u ∈ V, u ≠ slicePoint k ∧ IsClosed ({u} : Set ↥(Spec (.of (sliceRing k)))) := by
  have hprime : (Ideal.span {(X 0 : MvPolynomial (Fin 2) k)}).IsPrime :=
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 0)).mpr MvPolynomial.X_prime
  have : IsDomain (sliceRing k) := Ideal.Quotient.isDomain _
  have hclosed : IsClosed ({slicePoint k} : Set (PrimeSpectrum (sliceRing k))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr isMaximal_slicePoint
  have hgen : slicePoint k ∈
      closure ({⟨⊥, Ideal.isPrime_bot⟩} : Set (PrimeSpectrum (sliceRing k))) := by
    rw [PrimeSpectrum.closure_singleton]
    simp
  obtain ⟨x, hxV, hx⟩ := mem_closure_iff.mp hgen V hV hu₀
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (sliceRing k)) ∈ V := hx ▸ hxV
  obtain ⟨u, hu, hucl⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing
    (V \ {slicePoint k}) (hV.sdiff hclosed)
    ⟨⟨⊥, Ideal.isPrime_bot⟩, hbot, by
      intro hcontra
      exact mk_X_one_ne_zero (k := k)
        (Submodule.mem_bot _ |>.mp (hcontra ▸ mk_X_mem_slicePoint 1))⟩
  exact ⟨u, hu.1, hu.2, hucl⟩

/-! ### Axiom [5] fails -/

/-- The predicate negated below is the body of `Deformation.Artin.IsOpenVersality` for this
category, written out. That predicate takes a proof that the structure functor is fibred in
groupoids -- which the size-bounded site inclusion does not admit -- and does not use it. -/
private theorem isOpenVersality_eq_written_out (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))
    (hq : (artinAxiomsOver B hS).IsFiberedInGroupoids) :
    IsOpenVersality (artinAxiomsOver B hS) hq =
      ∀ (U : Over (Spec (.of (MvPolynomial (Fin 2) k)))), LocallyOfFiniteType U.hom →
        ∀ (x : artinAxiomsCategory k B hS)
          (hx : (artinAxiomsOver B hS).obj x = U) (u₀ : ↥U.left),
          IsFiniteTypePoint u₀ →
          IsVersalAt U (artinAxiomsOver B hS) u₀ x hx →
          ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
            ∀ u ∈ V.1, IsFiniteTypePoint u →
              IsVersalAt U (artinAxiomsOver B hS) u x hx := rfl

/-- **Openness of versality fails for the category of Tag 07XR**, written out: the slice is
versal at the origin, which is a finite-type point, but every open neighbourhood of the
origin contains a closed point at which it is not versal. Axiom [5] asks openness of
versality of the category and of its diagonal, so this is the failure of axiom [5]. -/
@[stacks 07XR "openness of versality fails for the category, hence axiom [5] fails"]
public theorem not_isOpenVersality_artinAxiomsCategory (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))) :
    ¬ ∀ (U : Over (Spec (.of (MvPolynomial (Fin 2) k)))), LocallyOfFiniteType U.hom →
        ∀ (x : artinAxiomsCategory k B hS)
          (hx : (artinAxiomsOver B hS).obj x = U) (u₀ : ↥U.left),
          IsFiniteTypePoint u₀ →
          IsVersalAt U (artinAxiomsOver B hS) u₀ x hx →
          ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
            ∀ u ∈ V.1, IsFiniteTypePoint u →
              IsVersalAt U (artinAxiomsOver B hS) u x hx := by
  intro h
  obtain ⟨V, hu₀V, hV⟩ := h (Over.mk (sliceImmersion k))
    (inferInstanceAs (LocallyOfFiniteType (sliceImmersion k))) (sliceObject B hS)
    (by delta sliceObject; rfl) (slicePoint k)
    (isFiniteTypePoint_of_isClosed_singleton
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal (slicePoint k)).mpr
        isMaximal_slicePoint))
    (isVersalAt_sliceObject B hS)
  obtain ⟨u, huV, hune, hucl⟩ :=
    exists_isClosed_singleton_mem_ne_slicePoint V.1 V.2 hu₀V
  exact not_isVersalAt_sliceObject u B hS hune
    (hV u huV (isFiniteTypePoint_of_isClosed_singleton hucl))

end Nonversal

end

end Deformation.Artin

end
