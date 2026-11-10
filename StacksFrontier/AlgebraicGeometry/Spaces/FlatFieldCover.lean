module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Flat covers of an algebraic space by the spectrum of a field

Let `Z` be an algebraic space over `S` admitting a surjective flat morphism from the spectrum
of a field. Tag 06QV says that then *every* morphism to `Z` from the spectrum of a field is
surjective and flat. Both clauses are proved here.

Surjectivity needs only the existence of a surjective field-valued morphism, and nothing
about `Z` beyond its being a presheaf: the point set of the presheaf represented by a field
spectrum over `S` is a singleton, so a surjective morphism out of it forces `|Z|` to be a
singleton, and then every morphism from a field spectrum is surjective on points.

Flatness of a morphism of algebraic spaces is the étale-chart condition
`AlgebraicGeometry.Space.IsFlat`, so proving it means proving that `U ⟶ V` is a flat morphism
of schemes for every commuting square of étale charts `U` of `Spec k'` and `V` of `Z`. The
argument reorganizes the source's proof so that only flatness, and not the descent lemma Tag
05VY, is needed:

* base changing the chart `V ⟶ Z` along the cover `Spec k ⟶ Z` gives a scheme `T` with
  `T ⟶ Spec k` étale, and `T ⟶ V` is flat because it sits in a commuting square of étale
  charts of the cover;
* surjectivity of the cover on points, together with a field-valued point of the chart `U` at
  a given `u`, produces a field `Ω` in the site and a morphism `Spec Ω ⟶ T` whose composite
  to `V` hits the image of `u`;
* `Spec Ω ⟶ T` is flat, because `Spec Ω ⟶ Spec k` is flat (every morphism to the spectrum of
  a field is) and flatness cancels against the weakly étale morphism `T ⟶ Spec k`;
* hence `Spec Ω ⟶ V` is flat, so the local ring of `V` at the image of `u` receives a flat
  local homomorphism to a field and is therefore itself a field;
* a morphism of schemes whose target has a field as local ring at every point in the image is
  flat.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isSurjective_of_fieldCover` is the surjectivity clause and
  `AlgebraicGeometry.Space.isFlat_of_fieldCover` the flatness clause of Tag 06QV.
* `AlgebraicGeometry.Space.subsingleton_points_yoneda_fieldSpec`: the point set of the
  presheaf represented by a field spectrum over `S` has at most one element.
* `AlgebraicGeometry.Space.exists_fieldSpec_at_point`: every point of a scheme in a big fppf
  site is the image of a morphism from the spectrum of a field which is again an object of
  the site, namely the residue field at that point.
* `AlgebraicGeometry.Space.presheaf_yoneda_map_of_inverseImage`: a morphism of the site whose
  underlying morphism of schemes has a base-change stable property satisfies the
  corresponding relatively representable property after Yoneda.
* `RingHom.Flat.isField_of_isField`: a local ring admitting a flat local homomorphism to a
  field is a field.
* `AlgebraicGeometry.flat_of_comp_of_weaklyEtale` and
  `AlgebraicGeometry.flat_of_isField_stalk`: the two scheme-level flatness criteria used.

## Implementation notes

That the point set of a field spectrum is a singleton is exactly the amalgamation statement
`AlgebraicGeometry.Space.exists_fieldSpec_common`: two field-valued points of the presheaf
represented by `Spec k` over `S` are two morphisms of field spectra to `Spec k` over `S`, and
a common extension of them inside the site is a common extension of the two representatives.

The field-valued point of a chart at a prescribed point is the spectrum of the residue field
there; it lies in the site because the residue field is a quotient of a localization of the
sections over an affine open, so Stacks 000R (9) applies.

Cancellation of flatness against a weakly étale morphism is `MorphismProperty.of_postcomp`
for the pair `(Flat, WeaklyEtale)`; the required `Q ≤ P.diagonal` is immediate from the
definition of `AlgebraicGeometry.WeaklyEtale`, whose second field is flatness of the
diagonal.

That a local ring with a flat local homomorphism to a field is a field is faithful flatness
of a flat local homomorphism (`Module.FaithfullyFlat.of_flat_of_isLocalHom`) plus injectivity
of the structure map: the maximal ideal lands in the zero ideal of the field.

## References

* [Stacks Project, Tag 06QV](https://stacks.math.columbia.edu/tag/06QV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

/-! ### Commutative algebra: flat local homomorphisms to a field -/

/-- A local ring admitting a flat local homomorphism to a field is itself a field.

A flat local homomorphism of local rings is faithfully flat, hence injective, and the
maximal ideal of the source lands in the maximal ideal of the target, which is zero. -/
theorem RingHom.Flat.isField_of_isField {A C : Type u} [CommRing A] [CommRing C]
    [IsLocalRing A] [IsLocalRing C] {φ : A →+* C} (hφ : φ.Flat) (hloc : IsLocalHom φ)
    (hC : IsField C) : IsField A := by
  algebraize [φ]
  have := hloc
  have : Module.FaithfullyFlat A C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro x hx
  refine FaithfulSMul.algebraMap_injective A C ?_
  rw [map_zero]
  have hmem : φ x ∈ IsLocalRing.maximalIdeal C := fun hu ↦ hx (isUnit_of_map_unit φ x hu)
  rwa [IsLocalRing.isField_iff_maximalIdeal_eq.mp hC, Ideal.mem_bot] at hmem

namespace AlgebraicGeometry

/-! ### Scheme-level flatness criteria -/

/-- Flatness of a composite can be cancelled by a weakly étale second factor: if `f ≫ g` is
flat and `g` is weakly étale, then `f` is flat.

This is `CategoryTheory.MorphismProperty.of_postcomp` for the pair `(Flat, WeaklyEtale)`; the
hypothesis it needs — that a weakly étale morphism has flat diagonal — is the second field of
`AlgebraicGeometry.WeaklyEtale`. -/
theorem flat_of_comp_of_weaklyEtale {X Y W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (hfg : Flat (f ≫ g)) (hg : WeaklyEtale g) : Flat f :=
  (MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    (fun _ _ _ hf ↦ hf.flat_diagonal)).of_postcomp f g hg hfg

/-- A morphism of schemes is flat as soon as the local ring of its target is a field at every
point of the image. Any module over a field is flat, so every stalk map is flat. -/
theorem flat_of_isField_stalk {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ x : X, IsField (Y.presheaf.stalk (f.base x))) : Flat f :=
  Flat.of_stalkMap f fun x ↦ RingHom.Flat.of_isField (h x) _

/-- The local rings of the spectrum of a field are fields: the spectrum of a field is an
integral scheme with one point, so its ring of global sections is a field, and the stalk is a
localization of that ring at a prime, hence the ring itself. -/
theorem isField_stalk_Spec_field (K : Type u) [Field K] (x : Spec (CommRingCat.of K)) :
    IsField ((Spec (CommRingCat.of K)).presheaf.stalk x) := by
  have hfield : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    isField_of_isIntegral_of_subsingleton (Spec (CommRingCat.of K))
  let _ : Field Γ(Spec (CommRingCat.of K), ⊤) := hfield.toField
  let _ := (Spec (CommRingCat.of K)).presheaf.algebra_section_stalk
    (U := (⊤ : (Spec (CommRingCat.of K)).Opens)) ⟨x, trivial⟩
  have hloc := (isAffineOpen_top (Spec (CommRingCat.of K))).isLocalization_stalk ⟨x, trivial⟩
  have hbij : Function.Bijective
      (algebraMap Γ(Spec (CommRingCat.of K), ⊤)
        ((Spec (CommRingCat.of K)).presheaf.stalk x)) :=
    IsField.localization_map_bijective
      (M := Ideal.primeCompl ((isAffineOpen_top (Spec (CommRingCat.of K))).primeIdealOf
        ⟨x, trivial⟩).asIdeal)
      (fun h ↦ h (Ideal.zero_mem _)) hfield
  exact MulEquiv.isField hfield (RingEquiv.ofBijective _ hbij).symm.toMulEquiv

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Field-valued points of a scheme in the site -/

/-- Every point of a scheme belonging to a big fppf site is the image of a morphism from the
spectrum of a field which is again an object of the site.

The field is the residue field at the point, whose spectrum satisfies the site's size cutoff
by Stacks 000R (9): the residue field is a quotient of the stalk, which is a localization of
the sections over an affine neighbourhood. -/
theorem exists_fieldSpec_at_point {X : Scheme.{u}} (hX : B.Contains X) (x : X) :
    ∃ (K : Type u) (_ : Field K), ∃ _ : B.Contains (Spec (.of K)),
      ∃ ρ : Spec (.of K) ⟶ X, ∀ y, ρ.base y = x := by
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  have hR : (Spec (CommRingCat.of ↥Γ(X, W))).size < B.cutoff := by
    refine lt_of_le_of_lt ?_ hX
    rw [Scheme.size_Spec]
    exact max_le X.aleph0_le_size (X.mk_sections_le_size ⟨W, hW⟩)
  let _ := X.presheaf.algebra_section_stalk (U := W) ⟨x, hxW⟩
  have hloc := hW.isLocalization_stalk ⟨x, hxW⟩
  have hstalk : #↥(X.presheaf.stalk x) ≤ max ℵ₀ #↥Γ(X, W) :=
    Cardinal.mk_le_of_isLocalization (Ideal.primeCompl (hW.primeIdealOf ⟨x, hxW⟩).asIdeal)
      ↥(X.presheaf.stalk x)
  have hres : #↥(X.residueField x) ≤ #↥(X.presheaf.stalk x) :=
    Cardinal.mk_le_of_surjective (f := IsLocalRing.residue ↥(X.presheaf.stalk x))
      Ideal.Quotient.mk_surjective
  refine ⟨↥(X.residueField x), inferInstance,
    Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hR
      (hres.trans hstalk), X.fromSpecResidueField x, fun y ↦ ?_⟩
  exact (Set.eq_singleton_iff_unique_mem.mp (X.range_fromSpecResidueField x)).2 _ ⟨y, rfl⟩

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes satisfies a
base-change stable property `P` satisfies the relatively representable property
`P.inverseImage ... |>.presheaf` after applying Yoneda.

The site has fibre products and its functor to schemes preserves them, so the inverse image
of `P` is again stable under base change and `CategoryTheory.MorphismProperty.relative_map`
applies. -/
theorem presheaf_yoneda_map_of_inverseImage {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderBaseChange) {U V : BigFppfOver B S hS} (φ : U ⟶ V)
    (hφ : P ((BigFppfOver.toScheme B S hS).map φ)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map φ) := by
  have : (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun hsq hg ↦ hP.of_isPullback (hsq.map (BigFppfOver.toScheme B S hS)) hg⟩
  exact MorphismProperty.relative_map hφ

/-! ### The point set of a field spectrum -/

/-- The presheaf on the big fppf site of `S` represented by the spectrum of a field has at
most one point: two field-valued representatives are two morphisms of field spectra over `S`
into it, and the amalgamation `AlgebraicGeometry.Space.exists_fieldSpec_common` provides a
common extension inside the site. -/
theorem subsingleton_points_yoneda_fieldSpec (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S) :
    Subsingleton (points B S hS (yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)))) := by
  refine ⟨fun x y ↦ ?_⟩
  induction x using Quot.ind with | _ p => ?_
  induction y using Quot.ind with | _ q => ?_
  refine Quot.sound ?_
  have hp : p.value.left.hom ≫ b = p.toBase := congrArg (fun k ↦ k.hom) (Over.w p.value)
  have hq : q.value.left.hom ≫ b = q.toBase := congrArg (fun k ↦ k.hom) (Over.w q.value)
  obtain ⟨Ω, instΩ, hΩ, ca, cb, key⟩ :=
    exists_fieldSpec_common B (K := p.carrier) (L := q.carrier) (M := k)
      p.contained q.contained p.value.left.hom q.value.left.hom
  have hbase : cb ≫ q.toBase = ca ≫ p.toBase := by
    rw [← hp, ← hq, ← Category.assoc, ← Category.assoc, key]
  let σ : (Over.mk (⟨ca ≫ p.toBase⟩ : B.obj hΩ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
      p.siteObject := Over.homMk (⟨ca⟩ : B.obj hΩ ⟶ B.obj p.contained) (by ext; rfl)
  let τ : (Over.mk (⟨ca ≫ p.toBase⟩ : B.obj hΩ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
      q.siteObject := Over.homMk (⟨cb⟩ : B.obj hΩ ⟶ B.obj q.contained) (by ext; exact hbase)
  refine ⟨{ carrier := Ω, contained := hΩ, toBase := ca ≫ p.toBase
            value := σ ≫ p.value }, ⟨σ, rfl⟩, ⟨τ, ?_⟩⟩
  change τ ≫ q.value = σ ≫ p.value
  ext
  exact key.symm

/-! ### Tag 06QV -/

/-- **Stacks 06QV**, surjectivity. If an algebraic space over `S` receives a surjective
morphism from the spectrum of a field, then every morphism to it from the spectrum of a field
is surjective.

Only the existence of the surjective field-valued morphism is used: it forces the point set of
the target to be a singleton, and the point set of a field spectrum is nonempty. -/
@[stacks 06QV "surjectivity"]
theorem isSurjective_of_fieldCover
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S)
    (f : yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) ⟶ Z)
    (hsurj : IsSurjective B S hS f)
    (k' : Type u) [Field k'] (hk' : B.Contains (Spec (.of k')))
    (b' : Spec (.of k') ⟶ S)
    (g : yoneda.obj (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS)) ⟶ Z) :
    IsSurjective B S hS g := by
  have hsrc := subsingleton_points_yoneda_fieldSpec B S hS k hk b
  have hZ : Subsingleton (points B S hS Z) := Function.Surjective.subsingleton hsurj
  intro z
  exact ⟨FieldValuedPoint.class B S hS _
    { carrier := k', contained := hk', toBase := b'
      value := id (α := (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS) : BigFppfOver B S hS) ⟶
        Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS)) (𝟙 _) }, Subsingleton.elim _ _⟩

/-- **Stacks 06QV**, flatness. If an algebraic space over `S` receives a surjective flat
morphism from the spectrum of a field, then every morphism to it from the spectrum of a field
is flat.

The algebraic-space hypothesis `_hZ` is retained from the source but is not needed: the
argument only uses that the chart `b₀` of `Z` is relatively representable and étale, which is
a hypothesis of the chart condition itself. -/
@[stacks 06QV "flatness"]
theorem isFlat_of_fieldCover
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hZ : IsAlgebraicSpace B S hS Z)
    (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
    (b : Spec (.of k) ⟶ S)
    (f : yoneda.obj (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS)) ⟶ Z)
    (hsurj : IsSurjective B S hS f)
    (hflat : IsFlat B S hS f)
    (k' : Type u) [Field k'] (hk' : B.Contains (Spec (.of k')))
    (b' : Spec (.of k') ⟶ S)
    (g : yoneda.obj (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS)) ⟶ Z) :
    IsFlat B S hS g := by
  intro U₀ V₀ a₀ b₀ h₀ ha₀ hb₀ hsq
  -- Base change the chart `b₀` of `Z` along the cover `f`; the result is étale over `Spec k`
  -- and flat over the chart `V₀`.
  have hTetale : Etale ((BigFppfOver.toScheme B S hS).map (hb₀.rep.snd f)) :=
    hb₀.property_snd f
  have hπ : Flat ((BigFppfOver.toScheme B S hS).map (hb₀.rep.fst' f)) :=
    hflat _ V₀ (yoneda.map (hb₀.rep.snd f)) b₀ (hb₀.rep.fst' f)
      (presheaf_yoneda_map_of_inverseImage B S hS Etale.etale_isStableUnderBaseChange _ hTetale)
      hb₀ (hb₀.rep.isPullback' f).w
  refine flat_of_isField_stalk _ fun u ↦ ?_
  -- A field-valued point of the chart `U₀` at `u`.
  obtain ⟨κ, instκ, hκ, ρ, hρ⟩ := exists_fieldSpec_at_point B U₀.left.2 u
  let σ : (Over.mk (⟨ρ ≫ U₀.hom.hom⟩ : B.obj hκ ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ U₀ :=
    Over.homMk (⟨ρ⟩ : B.obj hκ ⟶ U₀.left) (by ext; rfl)
  -- Surjectivity of the cover on points supplies a common field-valued extension.
  set p : FieldValuedPoint B S hS Z :=
    { carrier := κ, contained := hκ, toBase := ρ ≫ U₀.hom.hom
      value := yonedaEquiv (yoneda.map σ ≫ a₀ ≫ g) }
  obtain ⟨zq, hzq⟩ := hsurj (FieldValuedPoint.class B S hS Z p)
  obtain ⟨q, rfl⟩ := Quot.exists_rep zq
  rw [pointsMap_class, FieldValuedPoint.class_eq_class_iff] at hzq
  obtain ⟨r, ⟨α, hα⟩, ⟨β, hβ⟩⟩ := hzq
  -- The two composites out of the common extension agree in `Z`, so they factor through the
  -- base change.
  have hm : yonedaEquiv (yoneda.map (β ≫ σ ≫ h₀) ≫ b₀) = r.value := by
    rw [← hβ, show p.value = yonedaEquiv (yoneda.map σ ≫ a₀ ≫ g) from rfl,
      yonedaEquiv_naturality, ← hsq]
    simp
  have hqv : (FieldValuedPoint.map B S hS _ f q).value
      = yonedaEquiv (yoneda.map q.value ≫ f) := by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    rfl
  have hn : yonedaEquiv (yoneda.map (α ≫ q.value) ≫ f) = r.value := by
    rw [← hα, hqv, ← yonedaEquiv_naturality, ← yonedaEquiv_naturality,
      show (α ≫ q.value).op = q.value.op ≫ α.op from rfl]
    exact Functor.map_comp_apply Z q.value.op α.op (yonedaEquiv f)
  have hi : yoneda.map (β ≫ σ ≫ h₀) ≫ b₀ = yoneda.map (α ≫ q.value) ≫ f :=
    yonedaEquiv.injective (hm.trans hn.symm)
  have hwfst := hb₀.rep.lift'_fst (β ≫ σ ≫ h₀) (α ≫ q.value) hi
  -- The factorization is flat, because its composite to `Spec k` is and `T ⟶ Spec k` is
  -- weakly étale.
  have hwflat : Flat ((BigFppfOver.toScheme B S hS).map
      (hb₀.rep.lift' (β ≫ σ ≫ h₀) (α ≫ q.value) hi)) := by
    have h1 : Subsingleton ((BigFppfOver.toScheme B S hS).obj
        (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))) :=
      inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
    have h2 : IsIntegral ((BigFppfOver.toScheme B S hS).obj
        (Over.mk (⟨b⟩ : B.obj hk ⟶ B.obj hS))) :=
      inferInstanceAs (IsIntegral (Spec (CommRingCat.of k)))
    refine flat_of_comp_of_weaklyEtale _ ((BigFppfOver.toScheme B S hS).map (hb₀.rep.snd f))
      ?_ (etale_le_weaklyEtale _ _ _ hTetale)
    rw [← Functor.map_comp]
    infer_instance
  have hmflat : Flat ((BigFppfOver.toScheme B S hS).map (β ≫ σ ≫ h₀)) := by
    rw [← hwfst, Functor.map_comp]
    infer_instance
  -- Its image is the point of `V₀` under the chart, whose local ring is therefore a field.
  let pt : (BigFppfOver.toScheme B S hS).obj r.siteObject :=
    Classical.arbitrary (Spec (CommRingCat.of r.carrier))
  have hbase : ((BigFppfOver.toScheme B S hS).map (β ≫ σ ≫ h₀)).base pt
      = ((BigFppfOver.toScheme B S hS).map h₀).base u := by
    rw [Functor.map_comp, Functor.map_comp]
    change ((BigFppfOver.toScheme B S hS).map h₀).base
      (ρ.base (((BigFppfOver.toScheme B S hS).map β).base pt)) = _
    rw [hρ]
  rw [← hbase]
  exact RingHom.Flat.isField_of_isField
    (Flat.stalkMap ((BigFppfOver.toScheme B S hS).map (β ≫ σ ≫ h₀)) pt) inferInstance
    (isField_stalk_Spec_field r.carrier pt)

end Space

end AlgebraicGeometry

end
