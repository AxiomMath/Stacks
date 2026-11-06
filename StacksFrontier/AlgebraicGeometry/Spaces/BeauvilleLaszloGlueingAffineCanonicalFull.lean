module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalRestriction
import all StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful

/-!
# Fullness of the Beauville--Laszlo glueing functor on affine glueable spaces (Stacks 0F9Q)

Let `(g : R → R', f)` be a Beauville--Laszlo glueing pair and write `X = Spec R`,
`U = Spec R_f`, `X' = Spec R'` and `U' = Spec R'_f` for the four affine schemes of the
associated square of a big fppf site. The glueing functor of Stacks 0F9N restricts to a functor
`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction` from the affine algebraic spaces over
`X` that are glueable for `(g, f)` to the cartesian glueing triples with affine components. This
module proves that this functor is **full**, which is the surjectivity half of Stacks 0F9Q.

## Main results

* `BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction_full`: **Stacks 0F9Q**, fullness of the
  restricted glueing functor.

## Implementation notes

An affine glueable algebraic space over `X` is, by
`AlgebraicGeometry.BigFppfOver.exists_specOver`, isomorphic to the one attached to a ring map
`R → A`, and surjectivity of the action of a functor on a hom-set only depends on the source and
the target up to isomorphism, so everything reduces to a pair of rings `A` and `C` over `R`.

For such a pair the proof is a dictionary argument. The presheaf of points of `Spec A` over `X`,
restricted to `U`, is represented by the base change `Spec (A ⊗[R] R_f)`, and the universal
element of that representation is the *canonical section*
`BeauvilleLaszlo.Space.baseChangeSection`, the one given by the ring map
`A → A ⊗[R] R_f`; this is the content of
`AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso`, read on the identity of the
representing object. Consequently a morphism out of that restricted presheaf is determined by,
and determines, a single ring map out of `C` — recorded as `BeauvilleLaszlo.Space.sectRing` —
and the `U`- and `X'`-components of a morphism of glueing triples become ring maps
`u : C → A ⊗[R] R_f` and `v : C → A ⊗[R] R'` over `R`.

The commutative square of the morphism of glueing triples is what makes `u` and `v`
compatible. Its two structure arrows are the identity and the comparison
`BeauvilleLaszlo.Space.squareBaseChangeIso` of the two iterated base changes of the square,
which is a canonical cast and therefore acts on sections without changing the underlying
morphism of the site (`BeauvilleLaszlo.Space.sectLeft_squareBaseChangeIso`). Evaluating the
square on the canonical section over `Spec (A ⊗[R] R'_f)` and reading off the underlying ring
maps gives exactly the compatibility
`BeauvilleLaszlo.baseChangeToAway A f (v c) = BeauvilleLaszlo.localizedBaseChangeToAway A f (u c)`
of `StacksFrontier.RingTheory.BeauvilleLaszlo.GlueableModule`. Glueability of the ring `A` — which
comes from glueability of the space, tested on the identity chart, transported through
`AlgebraicGeometry.Scheme.ΓSpecIso` — then lets
`BeauvilleLaszlo.exists_unique_algHom_of_isGlueableFor` glue `u` and `v` to a ring map `C → A`
over `R`, and the two conclusions of that statement say precisely that the morphism it induces
has the prescribed `U`- and `X'`-components. A morphism of cartesian glueing triples is
determined by those two components, so the construction is a preimage.

The three base changes of `A` are taken to be the tensor products `A ⊗[R] R_f`, `A ⊗[R] R'` and
`A ⊗[R] R'_f`; `CommRingCat.isPushout_tensorProduct` turns each of them into the pushout square
that the dictionary of `StacksFrontier.AlgebraicGeometry.Spaces.AffineSiteSpecDictionary` wants,
and `AlgebraicGeometry.Scheme.size_pullback_lt` keeps their spectra inside the site. The
geometric half of the argument is carried out for an abstract square of rings
(`BeauvilleLaszlo.Space.map_surjective_of_glueing`) with the ring-theoretic glueing as a
hypothesis; this keeps every term in it small, which matters because the terms built from the
glueing functor are large enough that definitional unfolding of them is expensive.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9P](https://stacks.math.columbia.edu/tag/0F9P)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace BeauvilleLaszlo.Space

/-! ### Transport of surjectivity along isomorphisms -/

/-- Surjectivity of the action of a functor on a hom-set only depends on the source and the
target up to isomorphism. -/
private theorem map_surjective_of_iso {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {Y Z Y₀ Z₀ : C} (eY : Y ≅ Y₀) (eZ : Z ≅ Z₀)
    (h : Function.Surjective (F.map (X := Y₀) (Y := Z₀))) :
    Function.Surjective (F.map (X := Y) (Y := Z)) := by
  intro a
  obtain ⟨b, hb⟩ := h ((F.mapIso eY).inv ≫ a ≫ (F.mapIso eZ).hom)
  refine ⟨eY.hom ≫ b ≫ eZ.inv, ?_⟩
  rw [F.map_comp, F.map_comp, hb]
  simp only [Functor.mapIso_inv, Functor.mapIso_hom, ← F.map_comp_assoc, eY.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, ← F.map_comp,
    eZ.hom_inv_id, Category.comp_id]

/-! ### Sections of the restriction of a representable presheaf -/

section Sections

variable (B : BigFppfSite.{u}) {S X : Scheme.{u}} (hS : B.Contains S) (hX : B.Contains X)
  (j : B.obj hS ⟶ B.obj hX) (T T' : BigFppfOver B S hS) (W W' : BigFppfOver B X hX)

/-- A section over `T` of the restriction along `j` of the presheaf represented by `W`, read as
a morphism of the big fppf category over `X`. -/
private def sectHom (s : ((OverShriek.relocalizeRestrict j).obj (yoneda.obj W)).obj (op T)) :
    (Over.map j).obj T ⟶ W := s

/-- The morphism of the site underlying a section of a restricted representable presheaf. -/
private def sectLeft (s : ((OverShriek.relocalizeRestrict j).obj (yoneda.obj W)).obj (op T)) :
    T.left ⟶ W.left :=
  (sectHom B hS hX j T W s).left

/-- A section of a restricted representable presheaf is determined by its underlying morphism
of the site. -/
private theorem sect_ext {s t : ((OverShriek.relocalizeRestrict j).obj (yoneda.obj W)).obj (op T)}
    (h : sectLeft B hS hX j T W s = sectLeft B hS hX j T W t) : s = t :=
  Over.OverMorphism.ext h

/-- The section of a restricted representable presheaf attached to a morphism of the site
satisfying the structural triangle. -/
private def sectMk (m : T.left ⟶ W.left) (hm : m ≫ W.hom = T.hom ≫ j) :
    ((OverShriek.relocalizeRestrict j).obj (yoneda.obj W)).obj (op T) :=
  Over.homMk m hm

/-- The structural triangle satisfied by a section of a restricted representable presheaf. -/
private theorem sectLeft_comp_hom
    (s : ((OverShriek.relocalizeRestrict j).obj (yoneda.obj W)).obj (op T)) :
    sectLeft B hS hX j T W s ≫ W.hom = T.hom ≫ j :=
  (sectHom B hS hX j T W s).w

/-- Restricting a section along a morphism of the site composes the underlying morphisms. -/
private theorem sectLeft_map (κ : T ⟶ T')
    (s : ((OverShriek.relocalizeRestrict j).obj (yoneda.obj W)).obj (op T')) :
    sectLeft B hS hX j T W
        (((OverShriek.relocalizeRestrict j).obj (yoneda.obj W)).map κ.op s) =
      κ.left ≫ sectLeft B hS hX j T' W s :=
  rfl

/-- Pushing a section forward along the Yoneda image of a morphism of the site composes the
underlying morphisms. -/
private theorem sectLeft_yoneda_map (k : W ⟶ W')
    (s : ((OverShriek.relocalizeRestrict j).obj (yoneda.obj W)).obj (op T)) :
    sectLeft B hS hX j T W'
        (((OverShriek.relocalizeRestrict j).map (yoneda.map k)).app (op T) s) =
      sectLeft B hS hX j T W s ≫ k.left :=
  rfl

/-- The canonical identification of two restrictions along equal morphisms of the site does
not change the underlying morphism of a section. -/
private theorem sectLeft_eqToHom {j' : B.obj hS ⟶ B.obj hX} (hj : j = j')
    (s : ((OverShriek.relocalizeRestrict j).obj (yoneda.obj W)).obj (op T)) :
    sectLeft B hS hX j' T W
        ((eqToHom (congrArg
          (fun k => (OverShriek.relocalizeRestrict k).obj (yoneda.obj W)) hj)).app (op T) s) =
      sectLeft B hS hX j T W s := by
  subst hj
  rfl

end Sections

/-! ### Base change of rings -/

section RingData

open scoped TensorProduct

/-- **The spectrum of a base change of two contained rings is contained**: it is the fibre
product of their spectra. -/
private theorem contains_spec_tensorProduct (B : BigFppfSite.{u}) (R A S : Type u) [CommRing R]
    [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    (hA : B.Contains (Spec (.of A))) (hS : B.Contains (Spec (.of S))) :
    B.Contains (Spec (.of (A ⊗[R] S))) := by
  show (Spec (.of (A ⊗[R] S))).size < B.cutoff
  rw [← Scheme.size_congr (pullbackSpecIso R A S)]
  exact Scheme.size_pullback_lt _ _ hA hS

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (f : R)

/-- The map `R_f → R'_{f}` induced by `R → R'`, as a homomorphism of `R`-algebras. -/
private noncomputable def awayAlgHom :
    Localization.Away f →ₐ[R] Localization.Away (algebraMap R R' f) :=
  AlgHom.mk (Localization.awayMap (algebraMap R R') f) (by
    intro r
    change Localization.awayMap (algebraMap R R') f (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away (algebraMap R R' f)) r
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    exact (IsScalarTower.algebraMap_apply R R'
      (Localization.Away (algebraMap R R' f)) r).symm)

variable (A : Type u) [CommRing A] [Algebra R A]

/-- The base change to `R'_f` of the localization of `A` away from `f` is the map of
`StacksFrontier.RingTheory.BeauvilleLaszlo.GlueableModule`. -/
private theorem map_awayAlgHom_eq (z : A ⊗[R] Localization.Away f) :
    Algebra.TensorProduct.map (AlgHom.id R A) (awayAlgHom (R' := R') f) z =
      BeauvilleLaszlo.localizedBaseChangeToAway (S := R') A f z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, BeauvilleLaszlo.localizedBaseChangeToAway_tmul]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The base change to `R'_f` of the scalar extension of `A` to `R'` is the map of
`StacksFrontier.RingTheory.BeauvilleLaszlo.GlueableModule`. -/
private theorem map_toAlgHom_eq (z : A ⊗[R] R') :
    Algebra.TensorProduct.map (AlgHom.id R A)
        (IsScalarTower.toAlgHom R R' (Localization.Away (algebraMap R R' f))) z =
      BeauvilleLaszlo.baseChangeToAway (S := R') A f z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, BeauvilleLaszlo.baseChangeToAway_tmul]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end RingData

/-! ### The canonical section of a base change -/

section BaseChangeSection

variable (B : BigFppfSite.{u}) {Rc A C Sc As : CommRingCat.{u}} (hX : B.Contains (Spec Rc))
  (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C)) (hS : B.Contains (Spec Sc))
  (hAs : B.Contains (Spec As)) (φ : Rc ⟶ A) (ν : Rc ⟶ C) (ρ : Rc ⟶ Sc) (φs : Sc ⟶ As)

/-- The section of the restriction along `Spec ρ` of the presheaf of points of `Spec A`, over
the spectrum of a base change `As` of `A`, attached to a ring map `A ⟶ As` over `Rc`. -/
private noncomputable def baseChangeSection (ψ : A ⟶ As) (hw : φ ≫ ψ = ρ ≫ φs) :
    ((OverShriek.relocalizeRestrict
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
        (yoneda.obj (BigFppfOver.specOver B hX hA φ))).obj
      (op (BigFppfOver.specOver B hS hAs φs)) :=
  sectMk B hS hX (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
    (BigFppfOver.specOver B hS hAs φs) (BigFppfOver.specOver B hX hA φ)
    (ObjectProperty.homMk (Spec.map ψ) : B.obj hAs ⟶ B.obj hA) (by
      apply ObjectProperty.hom_ext
      change Spec.map ψ ≫ Spec.map φ = Spec.map φs ≫ Spec.map ρ
      rw [← Spec.map_comp, ← Spec.map_comp, hw])

/-- The morphism of the site underlying `BeauvilleLaszlo.Space.baseChangeSection`. -/
private theorem sectLeft_baseChangeSection (ψ : A ⟶ As) (hw : φ ≫ ψ = ρ ≫ φs) :
    sectLeft B hS hX (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
        (BigFppfOver.specOver B hS hAs φs) (BigFppfOver.specOver B hX hA φ)
        (baseChangeSection B hX hA hS hAs φ ρ φs ψ hw) =
      (ObjectProperty.homMk (Spec.map ψ) : B.obj hAs ⟶ B.obj hA) :=
  rfl

/-- **A section is the canonical section of the ring map it induces.** -/
private theorem eq_baseChangeSection
    (s : ((OverShriek.relocalizeRestrict
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
        (yoneda.obj (BigFppfOver.specOver B hX hC ν))).obj
      (op (BigFppfOver.specOver B hS hAs φs)))
    (θ : C ⟶ As) (hθ : ν ≫ θ = ρ ≫ φs)
    (hs : sectLeft B hS hX (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
        (BigFppfOver.specOver B hS hAs φs) (BigFppfOver.specOver B hX hC ν) s =
      (ObjectProperty.homMk (Spec.map θ) : B.obj hAs ⟶ B.obj hC)) :
    s = baseChangeSection B hX hC hS hAs ν ρ φs θ hθ :=
  sect_ext B hS hX (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
    (BigFppfOver.specOver B hS hAs φs) (BigFppfOver.specOver B hX hC ν)
    (hs.trans (sectLeft_baseChangeSection B hX hC hS hAs ν ρ φs θ hθ).symm)

/-- The ring map induced by a section of the restriction along `Spec ρ` of the presheaf of
points of `Spec C`, over the spectrum of a base change `As`. -/
private noncomputable def sectRing
    (s : ((OverShriek.relocalizeRestrict
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
        (yoneda.obj (BigFppfOver.specOver B hX hC ν))).obj
      (op (BigFppfOver.specOver B hS hAs φs))) : C ⟶ As :=
  Spec.preimage (B.inclusion.map
    (sectLeft B hS hX (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
      (BigFppfOver.specOver B hS hAs φs) (BigFppfOver.specOver B hX hC ν) s))

/-- `BeauvilleLaszlo.Space.sectRing` recovers the morphism of the site of a section. -/
private theorem specMap_sectRing
    (s : ((OverShriek.relocalizeRestrict
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
        (yoneda.obj (BigFppfOver.specOver B hX hC ν))).obj
      (op (BigFppfOver.specOver B hS hAs φs))) :
    sectLeft B hS hX (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
        (BigFppfOver.specOver B hS hAs φs) (BigFppfOver.specOver B hX hC ν) s =
      (ObjectProperty.homMk (Spec.map (sectRing B hX hC hS hAs ν ρ φs s)) :
        B.obj hAs ⟶ B.obj hC) :=
  ObjectProperty.hom_ext _ (Spec.map_preimage _).symm

/-- The triangle satisfied by `BeauvilleLaszlo.Space.sectRing`. -/
private theorem comp_sectRing
    (s : ((OverShriek.relocalizeRestrict
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
        (yoneda.obj (BigFppfOver.specOver B hX hC ν))).obj
      (op (BigFppfOver.specOver B hS hAs φs))) :
    ν ≫ sectRing B hX hC hS hAs ν ρ φs s = ρ ≫ φs := by
  have h := sectLeft_comp_hom B hS hX
    (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
    (BigFppfOver.specOver B hS hAs φs) (BigFppfOver.specOver B hX hC ν) s
  rw [specMap_sectRing] at h
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_comp]
  exact B.inclusion.congr_map h

/-- **The canonical section is the universal one.** The identity of the representing object
corresponds, under the base change isomorphism of
`AlgebraicGeometry.BigFppfOver.relocalizeRestrictSpecOverIso`, to the canonical section. -/
private theorem relocalizeRestrictSpecOverIso_inv_app_id (ψ : A ⟶ As)
    (hpo : IsPushout φ ρ ψ φs) :
    (BigFppfOver.relocalizeRestrictSpecOverIso B hX hA hS hAs φ ρ φs ψ hpo).inv.app
        (op (BigFppfOver.specOver B hS hAs φs))
        (𝟙 (BigFppfOver.specOver B hS hAs φs)) =
      baseChangeSection B hX hA hS hAs φ ρ φs ψ hpo.w := by
  refine eq_baseChangeSection B hX hA hS hAs φ ρ φs _ ψ hpo.w ?_
  have h1 : (BigFppfOver.relocalizeRestrictSpecOverIso B hX hA hS hAs φ ρ φs ψ hpo).inv.app
        (op (BigFppfOver.specOver B hS hAs φs))
        (𝟙 (BigFppfOver.specOver B hS hAs φs)) =
      (OverShriek.restrictYonedaIso
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
          (BigFppfOver.specOver B hX hA φ)).hom.app
        (op (BigFppfOver.specOver B hS hAs φs))
        (BigFppfOver.pullbackSpecOverIso B hX hA hS hAs φ ρ φs ψ hpo).inv := by
    show (OverShriek.restrictYonedaIso
        (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
        (BigFppfOver.specOver B hX hA φ)).hom.app
          (op (BigFppfOver.specOver B hS hAs φs))
          (𝟙 (BigFppfOver.specOver B hS hAs φs) ≫
            (BigFppfOver.pullbackSpecOverIso B hX hA hS hAs φ ρ φs ψ hpo).inv) = _
    rw [Category.id_comp]
  rw [h1]
  show ((OverShriek.restrictYonedaIso
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
      (BigFppfOver.specOver B hX hA φ)).hom.app
        (op (BigFppfOver.specOver B hS hAs φs))
        (BigFppfOver.pullbackSpecOverIso B hX hA hS hAs φ ρ φs ψ hpo).inv).left = _
  rw [OverShriek.restrictYonedaIso_hom_app_left,
    BigFppfOver.pullbackSpecOverIso_inv_left]
  exact (BigFppfOver.isPullback_specOver B hX hA hS hAs φ ρ φs ψ hpo).isoPullback_hom_fst

/-- **Two morphisms out of a restricted representable presheaf of an affine object agree as
soon as they agree on the canonical section.** -/
private theorem hom_ext_baseChangeSection (ψ : A ⟶ As) (hpo : IsPushout φ ρ ψ φs)
    {G : (BigFppfOver B (Spec Sc) hS)ᵒᵖ ⥤ Type u}
    (α β : (OverShriek.relocalizeRestrict
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
        (yoneda.obj (BigFppfOver.specOver B hX hA φ)) ⟶ G)
    (h : α.app (op (BigFppfOver.specOver B hS hAs φs))
          (baseChangeSection B hX hA hS hAs φ ρ φs ψ hpo.w) =
        β.app (op (BigFppfOver.specOver B hS hAs φs))
          (baseChangeSection B hX hA hS hAs φ ρ φs ψ hpo.w)) : α = β := by
  rw [← (BigFppfOver.relocalizeRestrictSpecOverIso B hX hA hS hAs φ ρ φs ψ hpo).cancel_iso_inv_left]
  apply yonedaEquiv.injective
  show α.app (op (BigFppfOver.specOver B hS hAs φs))
      ((BigFppfOver.relocalizeRestrictSpecOverIso B hX hA hS hAs φ ρ φs ψ hpo).inv.app
        (op (BigFppfOver.specOver B hS hAs φs))
        (𝟙 (BigFppfOver.specOver B hS hAs φs))) =
    β.app (op (BigFppfOver.specOver B hS hAs φs))
      ((BigFppfOver.relocalizeRestrictSpecOverIso B hX hA hS hAs φ ρ φs ψ hpo).inv.app
        (op (BigFppfOver.specOver B hS hAs φs))
        (𝟙 (BigFppfOver.specOver B hS hAs φs)))
  rw [relocalizeRestrictSpecOverIso_inv_app_id]
  exact h

end BaseChangeSection

/-- The morphism of the site given by `Spec.map` reverses the composition of ring maps. -/
private theorem homMk_spec_map_comp (B : BigFppfSite.{u}) {P Q T : CommRingCat.{u}}
    (hP : B.Contains (Spec P)) (hQ : B.Contains (Spec Q)) (hT : B.Contains (Spec T))
    (a : P ⟶ Q) (b : Q ⟶ T) :
    (ObjectProperty.homMk (Spec.map (a ≫ b)) : B.obj hT ⟶ B.obj hP) =
      (ObjectProperty.homMk (Spec.map b) : B.obj hT ⟶ B.obj hQ) ≫
        (ObjectProperty.homMk (Spec.map a) : B.obj hQ ⟶ B.obj hP) :=
  ObjectProperty.hom_ext _ (Spec.map_comp a b)

/-! ### Reading a morphism of base changes as a ring map -/

section ReadOff

variable (B : BigFppfSite.{u}) {Rc A C Sc As : CommRingCat.{u}} (hX : B.Contains (Spec Rc))
  (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C)) (hS : B.Contains (Spec Sc))
  (hAs : B.Contains (Spec As)) (φ : Rc ⟶ A) (ν : Rc ⟶ C) (ρ : Rc ⟶ Sc) (φs : Sc ⟶ As)

/-- **A morphism between the restrictions of two presheaves of points is the restriction of the
Yoneda image of a ring map**, as soon as it carries the canonical section to the composite with
that ring map. -/
private theorem relocalizeRestrict_map_eq_of_sectRing (ψA : A ⟶ As)
    (hpoA : IsPushout φ ρ ψA φs)
    (α : (OverShriek.relocalizeRestrict
            (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
          (yoneda.obj (BigFppfOver.specOver B hX hA φ)) ⟶
        (OverShriek.relocalizeRestrict
            (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
          (yoneda.obj (BigFppfOver.specOver B hX hC ν)))
    (χ : C ⟶ A) (hχ : ν ≫ χ = φ)
    (h : sectRing B hX hC hS hAs ν ρ φs
          (α.app (op (BigFppfOver.specOver B hS hAs φs))
            (baseChangeSection B hX hA hS hAs φ ρ φs ψA hpoA.w)) = χ ≫ ψA) :
    (OverShriek.relocalizeRestrict
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).map
        (yoneda.map ((BigFppfOver.specOverHomEquiv B hX hA hC φ ν).symm ⟨χ, hχ⟩)) = α := by
  refine hom_ext_baseChangeSection B hX hA hS hAs φ ρ φs ψA hpoA _ _ ?_
  refine sect_ext B hS hX (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
    (BigFppfOver.specOver B hS hAs φs) (BigFppfOver.specOver B hX hC ν) ?_
  rw [sectLeft_yoneda_map, sectLeft_baseChangeSection, specMap_sectRing, h,
    BigFppfOver.specOverHomEquiv_symm_left, homMk_spec_map_comp B _ hA]
  rfl

end ReadOff

/-! ### Reading the middle component of a morphism of glueing triples -/

section Middle

variable (B : BigFppfSite.{u}) {Rc A C Sc Tc As At : CommRingCat.{u}}
  (hX : B.Contains (Spec Rc)) (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C))
  (hS : B.Contains (Spec Sc)) (hT : B.Contains (Spec Tc)) (hAs : B.Contains (Spec As))
  (hAt : B.Contains (Spec At)) (φ : Rc ⟶ A) (ν : Rc ⟶ C) (ρ : Rc ⟶ Sc) (w : Sc ⟶ Tc)
  (φs : Sc ⟶ As) (ψA : A ⟶ As) (φt : Tc ⟶ At) (ψA' : A ⟶ At) (Ψ : As ⟶ At)

/-- **Restricting a morphism of base changes one step further composes the ring map with the
further base change.** -/
private theorem sectLeft_relocalizeRestrict_map (hpoA : IsPushout φ ρ ψA φs)
    (hΨ₂ : φs ≫ Ψ = w ≫ φt)
    (α : (OverShriek.relocalizeRestrict
            (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
          (yoneda.obj (BigFppfOver.specOver B hX hA φ)) ⟶
        (OverShriek.relocalizeRestrict
            (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
          (yoneda.obj (BigFppfOver.specOver B hX hC ν)))
    (sA : ((OverShriek.relocalizeRestrict
          ((ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS) ≫
            (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX))).obj
        (yoneda.obj (BigFppfOver.specOver B hX hA φ))).obj
      (op (BigFppfOver.specOver B hT hAt φt)))
    (hsA : sectLeft B hT hX
        ((ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS) ≫
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX))
        (BigFppfOver.specOver B hT hAt φt) (BigFppfOver.specOver B hX hA φ) sA =
      (ObjectProperty.homMk (Spec.map (ψA ≫ Ψ)) : B.obj hAt ⟶ B.obj hA)) :
    sectLeft B hT hX
        ((ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS) ≫
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX))
        (BigFppfOver.specOver B hT hAt φt) (BigFppfOver.specOver B hX hC ν)
        (((OverShriek.relocalizeRestrict
            (ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS)).map α).app
          (op (BigFppfOver.specOver B hT hAt φt)) sA) =
      (ObjectProperty.homMk (Spec.map (sectRing B hX hC hS hAs ν ρ φs
          (α.app (op (BigFppfOver.specOver B hS hAs φs))
            (baseChangeSection B hX hA hS hAs φ ρ φs ψA hpoA.w)) ≫ Ψ)) :
        B.obj hAt ⟶ B.obj hC) := by
  have hκ : (ObjectProperty.homMk (Spec.map Ψ) : B.obj hAt ⟶ B.obj hAs) ≫
      (BigFppfOver.specOver B hS hAs φs).hom =
      ((Over.map (ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS)).obj
        (BigFppfOver.specOver B hT hAt φt)).hom := by
    apply ObjectProperty.hom_ext
    show Spec.map Ψ ≫ Spec.map φs = Spec.map φt ≫ Spec.map w
    rw [← Spec.map_comp, ← Spec.map_comp, hΨ₂]
  set κ : (Over.map (ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS)).obj
      (BigFppfOver.specOver B hT hAt φt) ⟶ BigFppfOver.specOver B hS hAs φs :=
    Over.homMk (ObjectProperty.homMk (Spec.map Ψ)) hκ with hκdef
  have hκleft : κ.left = (ObjectProperty.homMk (Spec.map Ψ) : B.obj hAt ⟶ B.obj hAs) := rfl
  have h2 : sectLeft B hS hX (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
      ((Over.map (ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS)).obj
        (BigFppfOver.specOver B hT hAt φt)) (BigFppfOver.specOver B hX hA φ)
      (((OverShriek.relocalizeRestrict
            (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
          (yoneda.obj (BigFppfOver.specOver B hX hA φ))).map κ.op
        (baseChangeSection B hX hA hS hAs φ ρ φs ψA hpoA.w)) =
      (ObjectProperty.homMk (Spec.map (ψA ≫ Ψ)) : B.obj hAt ⟶ B.obj hA) := by
    rw [sectLeft_map, sectLeft_baseChangeSection, hκleft,
      homMk_spec_map_comp B _ hAs]
    rfl
  have hsA' : sA = ((OverShriek.relocalizeRestrict
        (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
      (yoneda.obj (BigFppfOver.specOver B hX hA φ))).map κ.op
      (baseChangeSection B hX hA hS hAs φ ρ φs ψA hpoA.w) := by
    refine sect_ext B hT hX _ _ _ ?_
    rw [hsA]
    exact h2.symm
  have h3 : sectLeft B hS hX (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)
      ((Over.map (ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS)).obj
        (BigFppfOver.specOver B hT hAt φt)) (BigFppfOver.specOver B hX hC ν)
      (α.app (op ((Over.map
            (ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS)).obj
          (BigFppfOver.specOver B hT hAt φt)))
        (((OverShriek.relocalizeRestrict
              (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX)).obj
            (yoneda.obj (BigFppfOver.specOver B hX hA φ))).map κ.op
          (baseChangeSection B hX hA hS hAs φ ρ φs ψA hpoA.w))) =
      (ObjectProperty.homMk (Spec.map (sectRing B hX hC hS hAs ν ρ φs
          (α.app (op (BigFppfOver.specOver B hS hAs φs))
            (baseChangeSection B hX hA hS hAs φ ρ φs ψA hpoA.w)) ≫ Ψ)) :
        B.obj hAt ⟶ B.obj hC) := by
    rw [NatTrans.naturality_apply α κ.op, sectLeft_map, specMap_sectRing, hκleft,
      homMk_spec_map_comp B _ hAs]
    rfl
  rw [hsA']
  exact h3

end Middle

/-! ### Glueability of the ring of an affine glueable space -/

section Glueability

open scoped TensorProduct

/-- **Glueability of the global sections of `Spec A` is glueability of `A`.** The ring of global
sections of `Spec A` is identified with `A` as an `R`-algebra by
`AlgebraicGeometry.Scheme.ΓSpecIso`, and glueability of a module only depends on it up to an
`R`-linear isomorphism. -/
theorem isGlueableFor_of_isGlueableGlobalSections
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
    (A : Type u) [CommRing A] [Algebra R A] (hA : B.Contains (Spec (.of A)))
    (hY : AlgebraicGeometry.Space.IsGlueableGlobalSections g f B hX
      (BigFppfOver.specOver B hX hA (CommRingCat.ofHom (algebraMap R A)))) :
    @BeauvilleLaszlo.IsGlueableFor R R' _ _ g.toAlgebra A _ _ f := by
  let _ : Algebra R R' := g.toAlgebra
  let _ : Algebra R Γ(Spec (CommRingCat.of A), ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop).hom).toAlgebra
  have h : BeauvilleLaszlo.IsGlueableFor (S := R') Γ(Spec (CommRingCat.of A), ⊤) f := hY
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A))).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom =
      CommRingCat.ofHom (algebraMap R A) := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact BeauvilleLaszlo.isGlueableFor_of_linearEquiv
    (AlgEquiv.ofRingEquiv (f := (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv)
      (ConcreteCategory.congr_hom key)).toLinearEquiv f h

end Glueability

/-! ### The structural arrow of the canonical glueing triple -/

section SquareCast

/-- A composite of morphisms of type-valued presheaves, applied to a section. -/
private theorem natTrans_comp_app_apply {C : Type*} [Category C] {F G H : C ⥤ Type u}
    (η : F ⟶ G) (θ : G ⟶ H) (T : C) (x : F.obj T) :
    (η ≫ θ).app T x = θ.app T (η.app T x) :=
  rfl

/-- Cancelling the identities on both sides of a commutative square whose two structure arrows
are identities. -/
private theorem eq_of_comp_id_eq_id_comp {C : Type*} [Category C] {Y Z : C} {m n : Y ⟶ Z}
    (h : m ≫ 𝟙 Z = 𝟙 Y ≫ n) : m = n := by
  simpa using h

/-- The canonical cast does not depend on the proof of the equality of objects. -/
private theorem eqToHom_eq_eqToHom {C : Type*} [Category C] {Y Z : C} (h h' : Y = Z) :
    eqToHom h = eqToHom h' :=
  rfl

/-- A canonical cast flanked by identities is again the canonical cast. -/
private theorem id_comp_eqToHom_comp_id {C : Type*} [Category C] {Y Z : C} (h h' : Y = Z) :
    (𝟙 Y ≫ eqToHom h) ≫ 𝟙 Z = eqToHom h' := by
  simp

/-- **The structural arrow of the canonical glueing triple is the canonical cast** attached to
the commutativity of the square. -/
private theorem squareBaseChangeIso_hom_app_hom (B : BigFppfSite.{u})
    (U' U X' X : Scheme.{u}) (hU' : B.Contains U') (hU : B.Contains U) (hX' : B.Contains X')
    (hX : B.Contains X) (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
    (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
    (hcomm : gU ≫ jU = gX' ≫ jX') (Y : AlgebraicSpaces B X hX) :
    ((squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).hom.app Y).hom =
      eqToHom (congrArg
        (fun k => (OverShriek.relocalizeRestrict k).obj Y.obj) hcomm) := by
  have h : (squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).hom.app Y =
      eqToHom (congrArg (fun k => (baseChange B U' X hU' hX k).obj Y) hcomm) := by
    simp only [squareBaseChangeIso, baseChangeIterToDirectIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
      eqToIso.hom, eqToHom_app]
    simp only [id, Iso.refl_hom, Iso.refl_inv]
    exact id_comp_eqToHom_comp_id _ _
  rw [h, fullSubcategory_eqToHom_hom]
  exact eqToHom_eq_eqToHom _ _

end SquareCast

/-! ### The components of the canonical glueing functor -/

section Components

variable (B : BigFppfSite.{u}) (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
  (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
  (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
  (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
  (hcomm : gU ≫ jU = gX' ≫ jX')

/-- The middle component of a morphism of canonical glueing triples is the base change of its
`U`-component: the inner structure arrows are identities. -/
private theorem glueingSpaces_hom_left_left {Y Z : AlgebraicSpaces B X hX}
    (a : (beauvilleLaszloGlueingSpaces B U' U X' X hU' hU hX' hX
        gU gX' jU jX' hcomm).functor.obj Y ⟶
      (beauvilleLaszloGlueingSpaces B U' U X' X hU' hU hX' hX
        gU gX' jU jX' hcomm).functor.obj Z) :
    a.hom.left.left = (baseChange B U' U hU' hU gU).map a.hom.left.right :=
  eq_of_comp_id_eq_id_comp a.hom.left.w

/-- **The commutative square of a morphism of canonical glueing triples.** -/
private theorem glueingSpaces_hom_w {Y Z : AlgebraicSpaces B X hX}
    (a : (beauvilleLaszloGlueingSpaces B U' U X' X hU' hU hX' hX
        gU gX' jU jX' hcomm).functor.obj Y ⟶
      (beauvilleLaszloGlueingSpaces B U' U X' X hU' hU hX' hX
        gU gX' jU jX' hcomm).functor.obj Z) :
    (baseChange B U' U hU' hU gU).map a.hom.left.right ≫
        (squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).hom.app Z =
      (squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).hom.app Y ≫
        (baseChange B U' X' hU' hX' gX').map a.hom.right := by
  rw [← glueingSpaces_hom_left_left]
  exact a.hom.w

/-- The `U`-component functor, on a morphism of glueing triples. -/
private theorem overU_map_eq {D E : GlueingData B U' U X' hU' hU hX' gU gX'} (a : D ⟶ E) :
    (overU B U' U X' hU' hU hX' gU gX').map a = a.hom.left.right :=
  rfl

/-- The `X'`-component functor, on a morphism of glueing triples. -/
private theorem overX'_map_eq {D E : GlueingData B U' U X' hU' hU hX' gU gX'} (a : D ⟶ E) :
    (overX' B U' U X' hU' hU hX' gU gX').map a = a.hom.right :=
  rfl

/-- The `U`-component of the image of a morphism under the canonical glueing functor. -/
private theorem overU_map_glueingSpaces_map {Y Z : AlgebraicSpaces B X hX} (k : Y ⟶ Z) :
    (overU B U' U X' hU' hU hX' gU gX').map
        ((beauvilleLaszloGlueingSpaces B U' U X' X hU' hU hX' hX
          gU gX' jU jX' hcomm).functor.map k) =
      (baseChange B U X hU hX jU).map k :=
  rfl

/-- The `X'`-component of the image of a morphism under the canonical glueing functor. -/
private theorem overX'_map_glueingSpaces_map {Y Z : AlgebraicSpaces B X hX} (k : Y ⟶ Z) :
    (overX' B U' U X' hU' hU hX' gU gX').map
        ((beauvilleLaszloGlueingSpaces B U' U X' X hU' hU hX' hX
          gU gX' jU jX' hcomm).functor.map k) =
      (baseChange B X' X hX' hX jX').map k :=
  rfl

/-- **The outer structure arrow acts on sections as the canonical cast.** -/
private theorem sectLeft_squareBaseChangeIso (W : BigFppfOver B X hX)
    (T : BigFppfOver B U' hU')
    (s : ((OverShriek.relocalizeRestrict (gU ≫ jU)).obj (yoneda.obj W)).obj (op T)) :
    sectLeft B hU' hX (gX' ≫ jX') T W
        (((squareBaseChangeIso B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).hom.app
            (schemeSpace W)).hom.app (op T) s) =
      sectLeft B hU' hX (gU ≫ jU) T W s := by
  rw [squareBaseChangeIso_hom_app_hom]
  exact sectLeft_eqToHom B hU' hX (gU ≫ jU) T W hcomm s

end Components

/-! ### The canonical section of an iterated base change -/

section IteratedSection

variable (B : BigFppfSite.{u}) {Rc A Sc Tc At : CommRingCat.{u}} (hX : B.Contains (Spec Rc))
  (hA : B.Contains (Spec A)) (hS : B.Contains (Spec Sc)) (hT : B.Contains (Spec Tc))
  (hAt : B.Contains (Spec At)) (φ : Rc ⟶ A) (ρ : Rc ⟶ Sc) (w : Sc ⟶ Tc) (φt : Tc ⟶ At)

/-- The canonical section of the twice-restricted presheaf of points of `Spec A`, over the
spectrum of a base change of `A` to `Tc`. -/
private noncomputable def iteratedBaseChangeSection (ψ : A ⟶ At)
    (hw : φ ≫ ψ = (ρ ≫ w) ≫ φt) :
    ((OverShriek.relocalizeRestrict
        ((ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS) ≫
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX))).obj
      (yoneda.obj (BigFppfOver.specOver B hX hA φ))).obj
    (op (BigFppfOver.specOver B hT hAt φt)) :=
  sectMk B hT hX
    ((ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS) ≫
      (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX))
    (BigFppfOver.specOver B hT hAt φt) (BigFppfOver.specOver B hX hA φ)
    (ObjectProperty.homMk (Spec.map ψ)) (by
      apply ObjectProperty.hom_ext
      change Spec.map ψ ≫ Spec.map φ = Spec.map φt ≫ (Spec.map w ≫ Spec.map ρ)
      simp only [← Spec.map_comp]
      rw [hw])

/-- The morphism of the site underlying
`BeauvilleLaszlo.Space.iteratedBaseChangeSection`. -/
private theorem sectLeft_iteratedBaseChangeSection (ψ : A ⟶ At)
    (hw : φ ≫ ψ = (ρ ≫ w) ≫ φt) :
    sectLeft B hT hX
        ((ObjectProperty.homMk (Spec.map w) : B.obj hT ⟶ B.obj hS) ≫
          (ObjectProperty.homMk (Spec.map ρ) : B.obj hS ⟶ B.obj hX))
        (BigFppfOver.specOver B hT hAt φt) (BigFppfOver.specOver B hX hA φ)
        (iteratedBaseChangeSection B hX hA hS hT hAt φ ρ w φt ψ hw) =
      (ObjectProperty.homMk (Spec.map ψ) : B.obj hAt ⟶ B.obj hA) :=
  rfl

end IteratedSection

/-! ### Fullness, from the ring-theoretic glueing -/

section Full

variable (B : BigFppfSite.{u}) {Rc A C Sf Sr St Af Ar At : CommRingCat.{u}}
  (hX : B.Contains (Spec Rc)) (hA : B.Contains (Spec A)) (hC : B.Contains (Spec C))
  (hU : B.Contains (Spec Sf)) (hX' : B.Contains (Spec Sr)) (hU' : B.Contains (Spec St))
  (φ : Rc ⟶ A) (ν : Rc ⟶ C) (ρf : Rc ⟶ Sf) (ρr : Rc ⟶ Sr) (ρt : Rc ⟶ St)
  (wf : Sf ⟶ St) (wr : Sr ⟶ St) (φf : Sf ⟶ Af) (ψf : A ⟶ Af) (φr : Sr ⟶ Ar) (ψr : A ⟶ Ar)
  (φt : St ⟶ At) (ψt : A ⟶ At) (Ψf : Af ⟶ At) (Ψr : Ar ⟶ At)

/-- **Fullness of the glueing functor on the spectra of two rings.** Suppose the square of
affine schemes of the site is `Spec` of a square of rings whose two composites `Rc → St` agree,
suppose `Af`, `Ar`, `At` are base changes of `A` to the three other bases compatible with that
square, and suppose that a pair of ring maps `C → Ar`, `C → Af` over `Rc` agreeing in `At` is
always induced by a ring map `C → A` over `Rc`. Then every morphism of glueing triples from the
triple of `Spec A` to the triple of `Spec C` comes from a morphism `Spec A → Spec C` over
`Spec Rc`.

The `U`- and `X'`-components of a given morphism of triples are read off as ring maps `C → Af`
and `C → Ar` by evaluating them on the canonical section of the corresponding base change; the
commutative square of the morphism of triples, evaluated on the canonical section over
`Spec At`, says that the two ring maps agree in `At`. The ring map `C → A` the hypothesis then
supplies induces the given morphism, because a morphism of triples is determined by its `U`-
and `X'`-components, and each of those is determined by its value on the canonical section. -/
private theorem map_surjective_of_glueing
    (hAf : B.Contains (Spec Af)) (hAR : B.Contains (Spec Ar)) (hAT : B.Contains (Spec At))
    (hcomm : (ObjectProperty.homMk (Spec.map wf) : B.obj hU' ⟶ B.obj hU) ≫
        (ObjectProperty.homMk (Spec.map ρf) : B.obj hU ⟶ B.obj hX) =
      (ObjectProperty.homMk (Spec.map wr) : B.obj hU' ⟶ B.obj hX') ≫
        (ObjectProperty.homMk (Spec.map ρr) : B.obj hX' ⟶ B.obj hX))
    (poF : IsPushout φ ρf ψf φf) (poR : IsPushout φ ρr ψr φr) (hρf : ρf ≫ wf = ρt)
    (hΨf : φf ≫ Ψf = wf ≫ φt) (hΨr : φr ≫ Ψr = wr ≫ φt)
    (hψf : ψf ≫ Ψf = ψt) (hψr : ψr ≫ Ψr = ψt) (hpoT : φ ≫ ψt = ρt ≫ φt)
    (hglue : ∀ (vv : C ⟶ Ar) (uu : C ⟶ Af), ν ≫ uu = ρf ≫ φf → ν ≫ vv = ρr ≫ φr →
      uu ≫ Ψf = vv ≫ Ψr → ∃ χ : C ⟶ A, ν ≫ χ = φ ∧ uu = χ ≫ ψf ∧ vv = χ ≫ ψr) :
    Function.Surjective
      ((beauvilleLaszloGlueingSpaces B (Spec St) (Spec Sf) (Spec Sr) (Spec Rc) hU' hU hX' hX
          (ObjectProperty.homMk (Spec.map wf) : B.obj hU' ⟶ B.obj hU)
          (ObjectProperty.homMk (Spec.map wr) : B.obj hU' ⟶ B.obj hX')
          (ObjectProperty.homMk (Spec.map ρf) : B.obj hU ⟶ B.obj hX)
          (ObjectProperty.homMk (Spec.map ρr) : B.obj hX' ⟶ B.obj hX) hcomm).functor.map
        (X := schemeSpace (BigFppfOver.specOver B hX hA φ))
        (Y := schemeSpace (BigFppfOver.specOver B hX hC ν))) := by
  intro a
  have hsqf : φ ≫ ψt = (ρf ≫ wf) ≫ φt := by rw [hρf]; exact hpoT
  set sf := a.hom.left.right.hom.app (op (BigFppfOver.specOver B hU hAf φf))
    (baseChangeSection B hX hA hU hAf φ ρf φf ψf poF.w)
  set sr := a.hom.right.hom.app (op (BigFppfOver.specOver B hX' hAR φr))
    (baseChangeSection B hX hA hX' hAR φ ρr φr ψr poR.w)
  set sA := iteratedBaseChangeSection B hX hA hU hU' hAT φ ρf wf φt ψt hsqf
  have hkey : sectRing B hX hC hU hAf ν ρf φf sf ≫ Ψf =
      sectRing B hX hC hX' hAR ν ρr φr sr ≫ Ψr := by
    have hh := congrArg (fun m => m.hom)
      (glueingSpaces_hom_w B (Spec St) (Spec Sf) (Spec Sr) (Spec Rc) hU' hU hX' hX
        (ObjectProperty.homMk (Spec.map wf) : B.obj hU' ⟶ B.obj hU)
        (ObjectProperty.homMk (Spec.map wr) : B.obj hU' ⟶ B.obj hX')
        (ObjectProperty.homMk (Spec.map ρf) : B.obj hU ⟶ B.obj hX)
        (ObjectProperty.homMk (Spec.map ρr) : B.obj hX' ⟶ B.obj hX) hcomm a)
    simp only [ObjectProperty.FullSubcategory.comp_hom] at hh
    have happ := (natTrans_comp_app_apply _ _ _ _).symm.trans
      ((ConcreteCategory.congr_hom
          (NatTrans.congr_app hh (op (BigFppfOver.specOver B hU' hAT φt)))
          sA).trans
        (natTrans_comp_app_apply _ _ _ _))
    have hfin := congrArg
      (sectLeft B hU' hX
        ((ObjectProperty.homMk (Spec.map wr) : B.obj hU' ⟶ B.obj hX') ≫
          (ObjectProperty.homMk (Spec.map ρr) : B.obj hX' ⟶ B.obj hX))
        (BigFppfOver.specOver B hU' hAT φt) (BigFppfOver.specOver B hX hC ν)) happ
    have e := fun W => sectLeft_squareBaseChangeIso B (Spec St) (Spec Sf) (Spec Sr) (Spec Rc)
      hU' hU hX' hX (ObjectProperty.homMk (Spec.map wf) : B.obj hU' ⟶ B.obj hU)
      (ObjectProperty.homMk (Spec.map wr) : B.obj hU' ⟶ B.obj hX')
      (ObjectProperty.homMk (Spec.map ρf) : B.obj hU ⟶ B.obj hX)
      (ObjectProperty.homMk (Spec.map ρr) : B.obj hX' ⟶ B.obj hX) hcomm W
      (BigFppfOver.specOver B hU' hAT φt)
    have e1 := e (BigFppfOver.specOver B hX hC ν)
      (((OverShriek.relocalizeRestrict
            (ObjectProperty.homMk (Spec.map wf) : B.obj hU' ⟶ B.obj hU)).map
          a.hom.left.right.hom).app (op (BigFppfOver.specOver B hU' hAT φt))
        sA)
    have e3 := e (BigFppfOver.specOver B hX hA φ) sA
    have e2 := sectLeft_relocalizeRestrict_map B hX hA hC hU hU' hAf hAT φ ν ρf wf φf ψf φt Ψf
      poF hΨf a.hom.left.right.hom
      sA ((sectLeft_iteratedBaseChangeSection B hX hA hU hU' hAT φ ρf wf φt ψt hsqf).trans
        (by rw [hψf]))
    have e4 := sectLeft_relocalizeRestrict_map B hX hA hC hX' hU' hAR hAT φ ν ρr wr φr ψr φt Ψr
      poR hΨr a.hom.right.hom
      (((squareBaseChangeIso B (Spec St) (Spec Sf) (Spec Sr) (Spec Rc) hU' hU hX' hX
              (ObjectProperty.homMk (Spec.map wf) : B.obj hU' ⟶ B.obj hU)
              (ObjectProperty.homMk (Spec.map wr) : B.obj hU' ⟶ B.obj hX')
              (ObjectProperty.homMk (Spec.map ρf) : B.obj hU ⟶ B.obj hX)
              (ObjectProperty.homMk (Spec.map ρr) : B.obj hX' ⟶ B.obj hX) hcomm).hom.app
            (schemeSpace (BigFppfOver.specOver B hX hA φ))).hom.app
        (op (BigFppfOver.specOver B hU' hAT φt)) sA)
      (e3.trans
        ((sectLeft_iteratedBaseChangeSection B hX hA hU hU' hAT φ ρf wf φt ψt hsqf).trans
          (by rw [hψr])))
    apply Spec.map_injective
    exact congrArg (fun m => m.hom) (e2.symm.trans (e1.symm.trans (hfin.trans e4)))
  obtain ⟨χ, hχ, hχf, hχr⟩ := hglue (sectRing B hX hC hX' hAR ν ρr φr sr)
    (sectRing B hX hC hU hAf ν ρf φf sf) (comp_sectRing B hX hC hU hAf ν ρf φf sf)
    (comp_sectRing B hX hC hX' hAR ν ρr φr sr) hkey
  refine ⟨schemeSpaceMap ((BigFppfOver.specOverHomEquiv B hX hA hC φ ν).symm ⟨χ, hχ⟩), ?_⟩
  refine glueingData_hom_ext B (Spec St) (Spec Sf) (Spec Sr) hU' hU hX'
    (ObjectProperty.homMk (Spec.map wf) : B.obj hU' ⟶ B.obj hU)
    (ObjectProperty.homMk (Spec.map wr) : B.obj hU' ⟶ B.obj hX') ?_ ?_
  · rw [overU_map_glueingSpaces_map, overU_map_eq]
    apply ObjectProperty.hom_ext
    exact relocalizeRestrict_map_eq_of_sectRing B hX hA hC hU hAf φ ν ρf φf ψf poF
      a.hom.left.right.hom χ hχ hχf
  · rw [overX'_map_glueingSpaces_map, overX'_map_eq]
    apply ObjectProperty.hom_ext
    exact relocalizeRestrict_map_eq_of_sectRing B hX hA hC hX' hAR φ ν ρr φr ψr poR
      a.hom.right.hom χ hχ hχr

end Full


/-! ### Fullness for the Beauville--Laszlo square -/

section Canonical

open scoped TensorProduct

/-- **Fullness of the glueing functor on the spectra of two rings, in the Beauville--Laszlo
square.** The three base changes of `A` are the tensor products `A ⊗[R] R_f`, `A ⊗[R] R'` and
`A ⊗[R] R'_f`, and the ring-theoretic input is
`BeauvilleLaszlo.exists_unique_algHom_of_isGlueableFor`. -/
private theorem map_surjective_specOver
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (f : R) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (algebraMap R R' f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU (algebraMap R R' : R →+* R') f B hU' hU ≫ canJU f B hU hX =
      canGX' (algebraMap R R' : R →+* R') f B hU' hX' ≫
        canJX' (algebraMap R R' : R →+* R') B hX' hX)
    (A C : Type u) [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))
    (hAglue : BeauvilleLaszlo.IsGlueableFor (S := R') A f) :
    Function.Surjective
      ((beauvilleLaszloGlueingSpaces B (Spec (.of (Localization.Away (algebraMap R R' f))))
          (Spec (.of (Localization.Away f))) (Spec (.of R')) (Spec (.of R)) hU' hU hX' hX
          (canGU (algebraMap R R' : R →+* R') f B hU' hU)
          (canGX' (algebraMap R R' : R →+* R') f B hU' hX') (canJU f B hU hX)
          (canJX' (algebraMap R R' : R →+* R') B hX' hX) hcomm).functor.map
        (X := schemeSpace (BigFppfOver.specOver B hX hA (CommRingCat.ofHom (algebraMap R A))))
        (Y := schemeSpace (BigFppfOver.specOver B hX hC
          (CommRingCat.ofHom (algebraMap R C))))) := by
  refine map_surjective_of_glueing B hX hA hC hU hX' hU'
    (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R C))
    (CommRingCat.ofHom (algebraMap R (Localization.Away f))) (CommRingCat.ofHom (algebraMap R R'))
    (CommRingCat.ofHom (algebraMap R (Localization.Away (algebraMap R R' f))))
    (CommRingCat.ofHom (awayAlgHom (R' := R') f).toRingHom)
    (CommRingCat.ofHom
      (IsScalarTower.toAlgHom R R' (Localization.Away (algebraMap R R' f))).toRingHom)
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
      (Localization.Away f) →+* A ⊗[R] (Localization.Away f)))
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] (Localization.Away f)))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : R' →+* A ⊗[R] R'))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R'))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
      (Localization.Away (algebraMap R R' f)) →+* A ⊗[R] (Localization.Away (algebraMap R R' f))))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      A →+* A ⊗[R] (Localization.Away (algebraMap R R' f))))
    (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R A)
      (awayAlgHom (R' := R') f)).toRingHom)
    (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R A)
      (IsScalarTower.toAlgHom R R' (Localization.Away (algebraMap R R' f)))).toRingHom)
    (contains_spec_tensorProduct B R A (Localization.Away f) hA hU)
    (contains_spec_tensorProduct B R A R' hA hX')
    (contains_spec_tensorProduct B R A (Localization.Away (algebraMap R R' f)) hA hU')
    hcomm (CommRingCat.isPushout_tensorProduct R A (Localization.Away f))
    (CommRingCat.isPushout_tensorProduct R A R') ?_ ?_ ?_ ?_ ?_
    (CommRingCat.isPushout_tensorProduct R A (Localization.Away (algebraMap R R' f))).w ?_
  · ext r
    exact (awayAlgHom (R' := R') f).commutes r
  · ext x
    simp
  · ext x
    simp
  · ext x
    simp
  · ext x
    simp
  · intro vv uu huu hvv hcp
    let uA : C →ₐ[R] A ⊗[R] (Localization.Away f) := AlgHom.mk uu.hom fun r =>
      (ConcreteCategory.congr_hom huu r).trans (Algebra.TensorProduct.includeRight.commutes r)
    let vA : C →ₐ[R] A ⊗[R] R' := AlgHom.mk vv.hom fun r =>
      (ConcreteCategory.congr_hom hvv r).trans (Algebra.TensorProduct.includeRight.commutes r)
    have hcompat : ∀ c : C, BeauvilleLaszlo.baseChangeToAway (S := R') A f (vA c) =
        BeauvilleLaszlo.localizedBaseChangeToAway (S := R') A f (uA c) := by
      intro c
      rw [← map_awayAlgHom_eq f A (uA c), ← map_toAlgHom_eq f A (vA c)]
      exact (ConcreteCategory.congr_hom hcp c).symm
    obtain ⟨hh, ⟨hh1, hh2⟩, -⟩ :=
      BeauvilleLaszlo.exists_unique_algHom_of_isGlueableFor f hAglue vA uA hcompat
    refine ⟨CommRingCat.ofHom hh.toRingHom, ?_, ?_, ?_⟩
    · ext r
      exact hh.commutes r
    · ext c
      exact (hh2 c).symm
    · ext c
      exact (hh1 c).symm

end Canonical

/-! ### The objective -/

section Objective

variable {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
  (B : BigFppfSite.{u})
  (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
  (hU : B.Contains (Spec (.of (Localization.Away f))))
  (hX' : B.Contains (Spec (.of R')))
  (hX : B.Contains (Spec (.of R)))
  (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)

/-- **Fullness**, the second half of Stacks 0F9Q for the affine subcategory: the glueing
functor of Stacks 0F9N is full on the affine algebraic spaces over `Spec R` which are glueable
for the pair `(g, f)`.

An affine glueable algebraic space is the spectrum of a ring, by
`AlgebraicGeometry.BigFppfOver.exists_specOver`, and surjectivity of the action on a hom-set
only depends on the source and the target up to isomorphism, so the statement reduces to the
spectra of two rings. Glueability of the space gives glueability of the ring of the
corresponding chart, and the ring-theoretic glueing
`BeauvilleLaszlo.exists_unique_algHom_of_isGlueableFor` then produces the morphism.

The glueing-pair hypothesis is not consumed: glueability of the source space already gives
glueability of the ring of its chart, and the ring-theoretic glueing asks for nothing more. It
is kept as a binder anyway, so that this statement presents the same interface as
`BeauvilleLaszlo.Space.canonicalAffineGlueableRestriction_faithful` and
`BeauvilleLaszlo.Space.affineGlueingEquivalenceOfParts`, exactly as
`AlgebraicGeometry.Space.exists_etaleCovering_iff_isGlueable` keeps its own unused copy. -/
theorem canonicalAffineGlueableRestriction_full
    (_hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) :
    (canonicalAffineGlueableRestriction g f B hU' hU hX' hX hcomm).Full := by
  let _ : Algebra R R' := g.toAlgebra
  constructor
  intro Y Z a
  obtain ⟨TA, hTA, ⟨eA⟩⟩ := Y.property.1
  obtain ⟨A, hA, φ, ⟨eA'⟩⟩ := BigFppfOver.exists_specOver B hX TA hTA
  obtain ⟨TC, hTC, ⟨eC⟩⟩ := Z.property.1
  obtain ⟨C, hC, ν, ⟨eC'⟩⟩ := BigFppfOver.exists_specOver B hX TC hTC
  let _ : Algebra R A := φ.hom.toAlgebra
  let _ : Algebra R C := ν.hom.toAlgebra
  have iA : Y.obj ≅ schemeSpace (BigFppfOver.specOver B hX hA φ) :=
    ObjectProperty.isoMk _ (eA ≪≫ yoneda.mapIso eA')
  have iC : Z.obj ≅ schemeSpace (BigFppfOver.specOver B hX hC ν) :=
    ObjectProperty.isoMk _ (eC ≪≫ yoneda.mapIso eC')
  have : IsIso iA.inv.hom := by
    show IsIso ((ObjectProperty.ι (IsAlgebraicSpace B (Spec (.of R)) hX)).map iA.inv)
    infer_instance
  have hAgs : AlgebraicGeometry.Space.IsGlueableGlobalSections g f B hX
      (BigFppfOver.specOver B hX hA φ) :=
    Y.property.2 (BigFppfOver.specOver B hX hA φ) iA.inv.hom
      (BigFppfOver.isAffine_toScheme_obj_specOver B hX hA φ)
      (AlgebraicGeometry.Space.isEtale_of_isIso B (Spec (.of R)) hX iA.inv.hom)
  have hsurj := map_surjective_of_iso
    (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _ hcomm).functor iA iC
    (map_surjective_specOver f B hU' hU hX' hX hcomm (A : Type u) (C : Type u) hA hC
      (isGlueableFor_of_isGlueableGlobalSections g f B hX (A : Type u) hA hAgs))
  obtain ⟨b, hb⟩ := hsurj a.hom
  exact ⟨ObjectProperty.homMk b, ObjectProperty.hom_ext _ hb⟩

end Objective

end BeauvilleLaszlo.Space

end
