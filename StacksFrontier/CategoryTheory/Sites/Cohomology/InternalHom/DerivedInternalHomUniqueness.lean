module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction

/-!
# The derived internal Hom on a ringed site is unique

Let `(C, O)` be a ringed site. `AlgebraicGeometry.RingedSite.DerivedInternalHom` is the datum of
a bifunctor on `D(Mod(O))`, contravariant in its source, whose value on a K-injective target is
the class of the ordinary internal Hom complex, naturally in both variables. This file shows
that datum to be unique: any two inhabitants have canonically isomorphic bifunctors, and the
isomorphism is the one the two model comparisons force on the classes of complexes with
K-injective target.

The consequence is that a derived internal Hom need not be *the* chosen one to be usable:
constructing any inhabitant of `DerivedInternalHom X` — by transport along an equivalence, say,
or by a different resolution — identifies it with
`AlgebraicGeometry.RingedSite.canonicalDerivedInternalHom`, hence with the bifunctor
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` that every statement of the library is
phrased in.

## Main definitions

* `AlgebraicGeometry.RingedSite.DerivedInternalHom.isoOfKInjective`: the comparison of two
  derived internal Homs on the classes of complexes with K-injective target, namely the
  composite of the two model comparisons.
* `AlgebraicGeometry.RingedSite.DerivedInternalHom.homIso`: the canonical isomorphism of the two
  bifunctors.
* `AlgebraicGeometry.RingedSite.DerivedInternalHom.isoDerivedSheafHomBifunctor`: that
  isomorphism against `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, which is the
  bifunctor the statements of the library are phrased in.

## Main results

* `AlgebraicGeometry.RingedSite.DerivedInternalHom.exists_hom_iso`: **uniqueness of the derived
  internal Hom.** The bifunctors of any two derived internal Homs are isomorphic by an
  isomorphism inducing `isoOfKInjective` on the classes of complexes with K-injective target.
* `AlgebraicGeometry.RingedSite.DerivedInternalHom.homIso_app_app` and
  `AlgebraicGeometry.RingedSite.DerivedInternalHom.homIso_app_app_homComparison`: the component
  of that isomorphism at such a class, and its compatibility with the two model comparisons;
  `DerivedInternalHom.isoDerivedSheafHomBifunctor_app_app_homComparison` is the same statement
  for the comparison with `derivedSheafHomBifunctor`.

## Implementation notes

Both bifunctors are uncurried to functors on `D(Mod(O))ᵒᵖ × D(Mod(O))`, where the comparison is
a single natural transformation and the pair of localization functors `Q.op` and `Q` is a single
localization functor `Q.op.prod Q`. The comparison is known only on the classes of complexes
whose target is K-injective, so it is extended to the whole derived category by
`AlgebraicGeometry.RingedSite.extendIsoFromResolution` along the functorial K-injective
resolution of Stacks 079P, exactly as the restriction comparison of Stacks 08JB is; the
extension is then curried back by the full faithfulness of uncurrying.

The naturality input is the `homComparison_natural` field of the two data: each of the two model
comparisons intertwines the maps induced on derived internal Hom with the maps `homMap` of
internal Hom complexes, so the composite of one with the inverse of the other intertwines the
two bifunctors.

Uniqueness is stated as the existence of an isomorphism with a prescribed family of components,
rather than as an equality of the two data, because the two bifunctors are genuinely different
objects: nothing identifies their values outside the classes of complexes with K-injective
target except this isomorphism.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u d

/-- Naturality transfers along a pair of isomorphisms into a common target: if `u` and `v` are
intertwined with one and the same map `w` by the isomorphisms `p` and the isomorphisms `q`, then
`u` and `v` are intertwined by the composites of the `p` with the inverses of the `q`. -/
private lemma comp_symm_naturality {D : Type*} [Category D] {A₁ A₂ B₁ B₂ Z₁ Z₂ : D}
    (u : A₁ ⟶ A₂) (v : B₁ ⟶ B₂) (p₁ : A₁ ≅ Z₁) (p₂ : A₂ ≅ Z₂) (q₁ : B₁ ≅ Z₁) (q₂ : B₂ ≅ Z₂)
    (w : Z₁ ⟶ Z₂) (hu : u ≫ p₂.hom = p₁.hom ≫ w) (hv : v ≫ q₂.hom = q₁.hom ≫ w) :
    u ≫ (p₂ ≪≫ q₂.symm).hom = (p₁ ≪≫ q₁.symm).hom ≫ v := by
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hu]
  simp only [Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← Category.assoc, ← hv, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {X : RingedSite.{u, u, u}}
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The comparison of two derived internal Homs on the class of a complex `A` and the class of a
K-injective complex `B`: there both of them are the class of the internal Hom complex
`SheafHom(A, B)`, by their model comparisons, so one is the other. -/
def DerivedInternalHom.isoOfKInjective (h₁ h₂ : DerivedInternalHom.{u, d} X)
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [instB : B.IsKInjective] :
    (h₁.hom.obj (op (DerivedCategory.Q.obj A))).obj (DerivedCategory.Q.obj B) ≅
      (h₂.hom.obj (op (DerivedCategory.Q.obj A))).obj (DerivedCategory.Q.obj B) :=
  h₁.homComparison A B ≪≫ (h₂.homComparison A B).symm

/-- **The derived internal Hom on a ringed site is unique.** The bifunctors of any two derived
internal Homs on `(C, O)` are isomorphic, by the isomorphism whose component on the class of a
complex `A` and the class of a K-injective complex `B` is the composite
`DerivedInternalHom.isoOfKInjective` of their two model comparisons.

Those components determine the isomorphism, since the classes of complexes with K-injective
target generate the derived category under the functorial K-injective resolution; the content of
the statement is that they cohere into a natural transformation at all, which is the naturality
of the two model comparisons. -/
theorem DerivedInternalHom.exists_hom_iso (h₁ h₂ : DerivedInternalHom.{u, d} X) :
    ∃ e : h₁.hom ≅ h₂.hom,
      ∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
        [B.IsKInjective],
        (e.hom.app (op (DerivedCategory.Q.obj A))).app (DerivedCategory.Q.obj B) =
          (h₁.isoOfKInjective h₂ A B).hom := by
  let C := CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ
  let Q : C ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    DerivedCategory.Q
  let W := HomologicalComplex.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)
  let R := (𝟭 Cᵒᵖ).prod (kInjectiveResolution X)
  let η : 𝟭 (Cᵒᵖ × C) ⟶ R :=
    { app := fun c => Prod.mkHom (𝟙 c.1) ((kInjectiveAugmentation X).app c.2)
      naturality := by
        intro c c' f
        apply Prod.ext
        · simp [R]
        · exact (kInjectiveAugmentation X).naturality f.2 }
  have (c : Cᵒᵖ × C) : IsIso ((Q.op.prod Q).map (η.app c)) := by
    dsimp [Q, η]
    exact (isIso_prod_iff _ _).2 ⟨(Q.mapIso (Iso.refl c.1.unop)).op.isIso_hom, inferInstance⟩
  obtain ⟨e, he⟩ := extendIsoFromResolution (Q.op.prod Q) (W.op.prod W) R η
    (fun c : Cᵒᵖ × C => c.2.IsKInjective)
    (fun c => Stacks.Injectives.kInjectiveResolutionFunctor_obj_isKInjective (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) c.2)
    (Functor.uncurry.obj h₁.hom) (Functor.uncurry.obj h₂.hom)
    (fun c hc => @DerivedInternalHom.homComparison _ _ h₁ c.1.unop c.2 hc ≪≫
      (@DerivedInternalHom.homComparison _ _ h₂ c.1.unop c.2 hc).symm)
    (by
      intro c c' hc hc' f
      have := hc
      have := hc'
      exact comp_symm_naturality _ _ _ _ _ _
        (DerivedCategory.Q.map (homMap X f.1.unop f.2))
        ((Category.assoc _ _ _).trans (h₁.homComparison_natural f.1.unop f.2))
        ((Category.assoc _ _ _).trans (h₂.homComparison_natural f.1.unop f.2)))
  refine ⟨Functor.fullyFaithfulUncurry.preimageIso e, fun A B _ => ?_⟩
  have ht := congrArg
    (fun k : Functor.uncurry.obj h₁.hom ⟶ Functor.uncurry.obj h₂.hom =>
      k.app (op (DerivedCategory.Q.obj A), DerivedCategory.Q.obj B))
    (Functor.fullyFaithfulUncurry.map_preimage (X := h₁.hom) (Y := h₂.hom) e.hom)
  exact ht.trans (he (op A, B) ‹B.IsKInjective›)

/-- The canonical isomorphism between the bifunctors of two derived internal Homs. -/
def DerivedInternalHom.homIso (h₁ h₂ : DerivedInternalHom.{u, d} X) : h₁.hom ≅ h₂.hom :=
  (DerivedInternalHom.exists_hom_iso h₁ h₂).choose

/-- On the class of a complex `A` and the class of a K-injective complex `B`, the canonical
isomorphism of two derived internal Homs is the composite of their two model comparisons. -/
theorem DerivedInternalHom.homIso_app_app (h₁ h₂ : DerivedInternalHom.{u, d} X)
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    (((h₁.homIso h₂).hom.app
        (op (DerivedCategory.Q.obj A))).app (DerivedCategory.Q.obj B)) =
      (h₁.isoOfKInjective h₂ A B).hom :=
  (DerivedInternalHom.exists_hom_iso h₁ h₂).choose_spec A B

/-- The canonical isomorphism of two derived internal Homs intertwines their model comparisons:
on the class of a complex `A` and the class of a K-injective complex `B` both data are the class
of the internal Hom complex `SheafHom(A, B)`, compatibly. -/
theorem DerivedInternalHom.homIso_app_app_homComparison (h₁ h₂ : DerivedInternalHom.{u, d} X)
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    (((h₁.homIso h₂).hom.app
          (op (DerivedCategory.Q.obj A))).app (DerivedCategory.Q.obj B)) ≫
        (h₂.homComparison A B).hom =
      (h₁.homComparison A B).hom := by
  rw [DerivedInternalHom.homIso_app_app]
  dsimp only [DerivedInternalHom.isoOfKInjective, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Any derived internal Hom is the derived internal Hom.** The bifunctor of an arbitrary
derived internal Hom datum on `(C, O)` is isomorphic to
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, the bifunctor the statements of the
library are phrased in.

This is the form in which uniqueness is consumed: it reduces a comparison with `RSheafHom(-, -)`
to the construction of *some* derived internal Hom datum, by transport along an equivalence or by
any other resolution. It is not the same as comparing with
`AlgebraicGeometry.RingedSite.canonicalDerivedInternalHom`, whose bifunctor is chosen by
`Classical.choice` and is therefore not identified with `derivedSheafHomBifunctor` by anything
weaker than this isomorphism. -/
def DerivedInternalHom.isoDerivedSheafHomBifunctor (h : DerivedInternalHom.{u, d} X) :
    h.hom ≅ derivedSheafHomBifunctor X :=
  h.homIso
    { hom := derivedSheafHomBifunctor X
      homComparison := fun A B _ => derivedSheafHomComparison X A B
      homComparison_natural := fun f g => derivedSheafHomComparison_naturality X f g }

/-- On the class of a complex `A` and the class of a K-injective complex `B`, the comparison of a
derived internal Hom datum with `RSheafHom(-, -)` intertwines the datum's model comparison with
the K-injective model comparison `AlgebraicGeometry.RingedSite.derivedSheafHomComparison`. -/
theorem DerivedInternalHom.isoDerivedSheafHomBifunctor_app_app_homComparison
    (h : DerivedInternalHom.{u, d} X)
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [B.IsKInjective] :
    ((h.isoDerivedSheafHomBifunctor.hom.app
          (op (DerivedCategory.Q.obj A))).app (DerivedCategory.Q.obj B)) ≫
        (derivedSheafHomComparison X A B).hom =
      (h.homComparison A B).hom :=
  h.homIso_app_app_homComparison _ A B

end AlgebraicGeometry.RingedSite

end
