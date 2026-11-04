module

public import StacksFrontier.AlgebraicGeometry.SectionsColimit.PullbackComp
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectCornerSquare

/-!
# The affine comparison of vector bundles is compatible with composition of ring maps

`Stacks.AlgebraicGeometry.SectionsColimit.tildePullbackIso_comp_app` is the compatibility of the
affine base-change isomorphism `M ↦ M^~` with composition of ring maps, on all sheaves of
modules. This file transports it to the comparison
`AlgebraicGeometry.tildeVectPullbackIso` of finite projective modules with vector bundles, which
is the form the gluing of Stacks Tag 0EXC consumes.

## Main results

* `AlgebraicGeometry.tildeVectPullbackIso_comp_app`: **the affine comparison of vector bundles
  is compatible with composition of ring maps.**
* `AlgebraicGeometry.tildeVectPullbackIso_corner`: **the affine content of the compatibility over
  the exceptional corner of Stacks Tag 0EXC** — the hypothesis which
  `AlgebraicGeometry.vectCornerFlat` abstracts.
* `AlgebraicGeometry.specIter_squareIter_inv`: **the inverse iterated Frobenius comparison on an
  affine leg is the comparison attached to the square of the two `p ^ N`-power morphisms** — the
  form in which the Frobenius twists of the compatibility over the exceptional corner are fed to
  `AlgebraicGeometry.vectCornerFlat`.

## Implementation notes

The transport is *not* the one-line `CategoryTheory.ObjectProperty.hom_ext` it looks like, and the
reason is worth recording.

`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is a `CategoryTheory.eqToIso`, so its components
are built with `Eq.rec`. Whenever the kernel has to put such a component in weak head normal form
— which it does as soon as it must compare one with anything not syntactically identical to it —
it attempts the K-like reduction of that `Eq.rec`, and for that it asks whether the two morphisms
of schemes indexing the equality are *definitionally* equal. For the equality
`Spec.map (φ ≫ ψ) = Spec.map ψ ≫ Spec.map φ` the answer is no, and finding that out exhausts the
kernel's budget: the naive transport of the coherence to vector bundles dies with a deterministic
timeout, and so does the one-step bridge
`(Scheme.Modules.pullbackCongr hsq).hom.app ((tildeVect R).obj L).obj =
  (Scheme.Modules.pullbackCongr hsq).hom.app ((tilde.functor R).obj L.obj)`,
even with the equality proof left a variable.

The fix is to leave the *morphism* a variable: the statement below compares the restrictions along
a variable `k : Spec T ⟶ Spec R` with the two composites, so the K-like reduction fails at once
and the kernel compares the two spellings of the sheaf by congruence, which is cheap. Consumers
instantiate `k := Spec.map (φ ≫ ψ)` with `hk := rfl` and remove the resulting
`AlgebraicGeometry.Scheme.Vect.pullbackCongr` of `rfl` with
`AlgebraicGeometry.vectPullbackCongr_refl_hom_app`; instantiation costs nothing, because no
further definitional comparison is asked for.

## References

* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.AlgebraicGeometry.SectionsColimit

universe u

namespace AlgebraicGeometry

variable {R S T : CommRingCat.{u}}

/-- `ModuleGlueing.extendScalarsComp`, which the comparison
`AlgebraicGeometry.FinProj.extendScalarsComp` on finite projective modules is built from, is
`ModuleCat.extendScalarsComp`: the two are the same construction, the former stated for rings in
independent universes. -/
lemma moduleGlueing_extendScalarsComp_eq (φ : R ⟶ S) (ψ : S ⟶ T) :
    ModuleGlueing.extendScalarsComp.{u, u, u, u} φ.hom ψ.hom =
      ModuleCat.extendScalarsComp φ.hom ψ.hom :=
  rfl

/-- **The affine base-change isomorphism is compatible with composition of ring maps**, with the
restriction along the composite taken along a morphism of schemes given only up to equality. -/
theorem tildePullbackIso_comp_app_of (φ : R ⟶ S) (ψ : S ⟶ T) (M : ModuleCat.{u} R)
    {k : Spec T ⟶ Spec R} (hk : k = Spec.map (φ ≫ ψ))
    (hk' : k = Spec.map ψ ≫ Spec.map φ) :
    ((Scheme.Modules.pullbackCongr hk').hom.app ((tilde.functor R).obj M) ≫
          (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).inv.app
            ((tilde.functor R).obj M)) ≫
        (Scheme.Modules.pullback (Spec.map ψ)).map ((tildePullbackIso φ).hom.app M) ≫
          (tildePullbackIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) =
      (Scheme.Modules.pullbackCongr hk).hom.app ((tilde.functor R).obj M) ≫
        (tildePullbackIso (φ ≫ ψ)).hom.app M ≫
          (tilde.functor T).map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M) := by
  subst hk
  obtain rfl : hk' = Spec.map_comp φ ψ := rfl
  rw [modulesPullbackCongr_refl_hom_app, Category.id_comp]
  exact tildePullbackIso_comp_app φ ψ M

/-- **The affine comparison of vector bundles is compatible with composition of ring maps.**
Restricting `L^~` along `Spec.map φ` and then along `Spec.map ψ`, and comparing with
`(T ⊗_S (S ⊗_R L))^~` in two steps, is the same as restricting along `Spec.map (φ ≫ ψ)` in one
step and splitting `T ⊗_R L` as `T ⊗_S (S ⊗_R L)`.

The restriction along the composite is taken along a morphism `k` of schemes given only up to
equality; see the implementation notes for why. -/
theorem tildeVectPullbackIso_comp_app (φ : R ⟶ S) (ψ : S ⟶ T) (L : FinProj R)
    {k : Spec T ⟶ Spec R} (hk : k = Spec.map (φ ≫ ψ))
    (hk' : k = Spec.map ψ ≫ Spec.map φ) :
    ((Scheme.Vect.pullbackCongr hk').hom.app ((tildeVect R).obj L) ≫
          (Scheme.Vect.pullbackComp (Spec.map ψ) (Spec.map φ)).inv.app ((tildeVect R).obj L)) ≫
        (Scheme.Vect.pullback (Spec.map ψ)).map ((tildeVectPullbackIso φ).hom.app L) ≫
          (tildeVectPullbackIso ψ).hom.app ((FinProj.extendScalars φ).obj L) =
      (Scheme.Vect.pullbackCongr hk).hom.app ((tildeVect R).obj L) ≫
        (tildeVectPullbackIso (φ ≫ ψ)).hom.app L ≫
          (tildeVect T).map ((FinProj.extendScalarsComp φ ψ).hom.app L) := by
  refine ObjectProperty.hom_ext _ ?_
  simp only [ObjectProperty.FullSubcategory.comp_hom, Scheme.Vect.pullback_obj_obj,
    Scheme.Vect.pullback_map_hom, Scheme.Vect.pullbackCongr_hom_app_hom,
    Scheme.Vect.pullbackComp_inv_app_hom, tildeVect_obj_obj, tildeVect_map_hom,
    tildeVectPullbackIso_hom_app_hom, FinProj.extendScalars_obj_obj,
    FinProj.extendScalarsComp_hom_app_hom, moduleGlueing_extendScalarsComp_eq]
  exact tildePullbackIso_comp_app_of φ ψ L.obj hk hk'

/-! ### Extension of scalars along a composite given up to equality -/

namespace FinProj

/-- **Extension of scalars along a composite, with the composite given only up to equality.** -/
noncomputable def extendScalarsCompOf (φ : R ⟶ S) (ψ : S ⟶ T) (χ : R ⟶ T) (hχ : φ ≫ ψ = χ) :
    extendScalars χ ≅ extendScalars φ ⋙ extendScalars ψ :=
  extendScalarsCongr hχ.symm ≪≫ extendScalarsComp φ ψ

/-- The comparison of `AlgebraicGeometry.FinProj.extendScalarsCompOf` at an object. -/
lemma extendScalarsCompOf_hom_app (φ : R ⟶ S) (ψ : S ⟶ T) (χ : R ⟶ T) (hχ : φ ≫ ψ = χ)
    (L : FinProj R) :
    (extendScalarsCompOf φ ψ χ hχ).hom.app L =
      (extendScalarsCongr hχ.symm).hom.app L ≫ (extendScalarsComp φ ψ).hom.app L :=
  rfl

/-- Extension of scalars along a morphism, transported along an equality which holds because the
two morphisms are the same term, is the identity. -/
lemma extendScalarsCongr_refl_hom_app {φ : R ⟶ S} (h : φ = φ) (L : FinProj R) :
    (extendScalarsCongr h).hom.app L = 𝟙 _ := by
  obtain rfl : h = rfl := rfl
  refine ObjectProperty.hom_ext _ ?_
  simp [extendScalarsCongr_hom_app_hom]

/-- **Transport of extension of scalars along equal ring maps is compatible with transitivity.**
The composite equality is taken as a hypothesis rather than built from the two given ones,
because the built proof term is what the kernel has to recheck at every use. -/
lemma extendScalarsCongr_trans_hom_app {φ ψ χ : R ⟶ S} (e : φ = ψ) (e' : ψ = χ) (e'' : φ = χ)
    (L : FinProj R) :
    (extendScalarsCongr e).hom.app L ≫ (extendScalarsCongr e').hom.app L =
      (extendScalarsCongr e'').hom.app L := by
  subst e
  subst e'
  obtain rfl : e'' = rfl := rfl
  rw [extendScalarsCongr_refl_hom_app, Category.comp_id]

end FinProj

/-- The comparison of `AlgebraicGeometry.FinProj.extendScalarsCompOf` when the composite is given
as the composite itself. -/
lemma extendScalarsCompOf_rfl_hom_app (φ : R ⟶ S) (ψ : S ⟶ T) (L : FinProj R) :
    (FinProj.extendScalarsCompOf φ ψ (φ ≫ ψ) rfl).hom.app L =
      (FinProj.extendScalarsComp φ ψ).hom.app L := by
  rw [FinProj.extendScalarsCompOf_hom_app, FinProj.extendScalarsCongr_refl_hom_app,
    Category.id_comp]

/-- **The affine comparison of vector bundles is compatible with composition of ring maps**, with
the composite ring map given only up to equality, and the restriction along it taken along a
morphism of schemes given only up to equality. -/
theorem tildeVectPullbackIso_comp_app_of (φ : R ⟶ S) (ψ : S ⟶ T) (χ : R ⟶ T) (hχ : φ ≫ ψ = χ)
    (L : FinProj R) {k : Spec T ⟶ Spec R} (hk : k = Spec.map χ)
    (hk' : k = Spec.map ψ ≫ Spec.map φ) :
    ((Scheme.Vect.pullbackCongr hk').hom.app ((tildeVect R).obj L) ≫
          (Scheme.Vect.pullbackComp (Spec.map ψ) (Spec.map φ)).inv.app ((tildeVect R).obj L)) ≫
        (Scheme.Vect.pullback (Spec.map ψ)).map ((tildeVectPullbackIso φ).hom.app L) ≫
          (tildeVectPullbackIso ψ).hom.app ((FinProj.extendScalars φ).obj L) =
      (Scheme.Vect.pullbackCongr hk).hom.app ((tildeVect R).obj L) ≫
        (tildeVectPullbackIso χ).hom.app L ≫
          (tildeVect T).map ((FinProj.extendScalarsCompOf φ ψ χ hχ).hom.app L) := by
  subst hχ
  rw [extendScalarsCompOf_rfl_hom_app]
  exact tildeVectPullbackIso_comp_app φ ψ L hk hk'

/-! ### The affine comparison over the exceptional corner -/

/-- **The affine content of the compatibility over the exceptional corner of Stacks Tag 0EXC.**
Let `r₁ : R ⟶ S₁` and `r₂ : R ⟶ S₂` be the two maps out of the upper-left corner of a commuting
square of rings and `ε₁ : S₁ ⟶ T`, `ε₂ : S₂ ⟶ T` the two maps into the lower-right corner, with
`q` the common composite. Then, for a finite projective `R`-module `L` and any identification `κ`
of its two iterated extensions of scalars to `T` which is compatible with the two canonical ones,
the two restrictions of `L^~` to `Spec T` agree: the comparison of
`AlgebraicGeometry.tildeVectPullbackIso` for `r₁` read on `Spec T` is the comparison for `r₂`
transported by `κ`, through the pseudofunctoriality of restriction.

This is the hypothesis which `AlgebraicGeometry.vectCornerFlat` abstracts. -/
theorem tildeVectPullbackIso_corner {S₁ S₂ : CommRingCat.{u}} (r₁ : R ⟶ S₁) (r₂ : R ⟶ S₂)
    (ε₁ : S₁ ⟶ T) (ε₂ : S₂ ⟶ T) (q : R ⟶ T) (hq₁ : r₁ ≫ ε₁ = q) (hq₂ : r₂ ≫ ε₂ = q)
    (L : FinProj R)
    (κ : (FinProj.extendScalars r₂ ⋙ FinProj.extendScalars ε₂).obj L ⟶
      (FinProj.extendScalars r₁ ⋙ FinProj.extendScalars ε₁).obj L)
    (hκ : (FinProj.extendScalarsCompOf r₂ ε₂ q hq₂).hom.app L ≫ κ =
      (FinProj.extendScalarsCompOf r₁ ε₁ q hq₁).hom.app L)
    (hv : Spec.map ε₁ ≫ Spec.map r₁ = Spec.map ε₂ ≫ Spec.map r₂) :
    (Scheme.Vect.pullback (Spec.map ε₁)).map ((tildeVectPullbackIso r₁).hom.app L) ≫
        (tildeVectPullbackIso ε₁).hom.app ((FinProj.extendScalars r₁).obj L) =
      ((Scheme.Vect.pullbackComp (Spec.map ε₁) (Spec.map r₁)).hom.app ((tildeVect R).obj L) ≫
          (Scheme.Vect.pullbackCongr hv).hom.app ((tildeVect R).obj L) ≫
            (Scheme.Vect.pullbackComp (Spec.map ε₂) (Spec.map r₂)).inv.app
              ((tildeVect R).obj L)) ≫
        (Scheme.Vect.pullback (Spec.map ε₂)).map ((tildeVectPullbackIso r₂).hom.app L) ≫
          (tildeVectPullbackIso ε₂).hom.app ((FinProj.extendScalars r₂).obj L) ≫
            (tildeVect T).map κ := by
  have hk'c : Spec.map q = Spec.map ε₁ ≫ Spec.map r₁ :=
    (congrArg Spec.map hq₁.symm).trans (Spec.map_comp r₁ ε₁)
  have hk'm : Spec.map q = Spec.map ε₂ ≫ Spec.map r₂ :=
    (congrArg Spec.map hq₂.symm).trans (Spec.map_comp r₂ ε₂)
  have hc := tildeVectPullbackIso_comp_app_of r₁ ε₁ q hq₁ L (rfl : Spec.map q = Spec.map q) hk'c
  have hm := tildeVectPullbackIso_comp_app_of r₂ ε₂ q hq₂ L (rfl : Spec.map q = Spec.map q) hk'm
  rw [vectPullbackCongr_refl_hom_app, Category.id_comp] at hc hm
  rw [← cancel_epi ((Scheme.Vect.pullbackCongr hk'c).hom.app ((tildeVect R).obj L) ≫
      (Scheme.Vect.pullbackComp (Spec.map ε₁) (Spec.map r₁)).inv.app ((tildeVect R).obj L)), hc]
  simp only [Category.assoc] at hm ⊢
  rw [Iso.inv_hom_id_app_assoc,
    reassoc_of% (vectPullbackCongr_trans_hom_app hk'c hv hk'm ((tildeVect R).obj L)),
    reassoc_of% hm, ← CategoryTheory.Functor.map_comp, hκ]

/-! ### The Frobenius leg of the exceptional corner -/

section Frobenius

open Stacks.Frobenius

variable {X Y : Scheme.{u}}

/-- **The inverses of a commuting square of isomorphisms commute**, as a statement of pure
category theory with the four inverses and the inverse laws it needs given as data. -/
lemma inv_step_aux {C : Type*} [Category C] {U V W Z : C} (Sh : U ⟶ V) (Si : V ⟶ U)
    (Gh : V ⟶ W) (Gi : W ⟶ V) (Fh : U ⟶ Z) (Fi : Z ⟶ U) (Lh : Z ⟶ W) (Li : W ⟶ Z)
    (hS : Sh ≫ Si = 𝟙 U) (hG : Gh ≫ Gi = 𝟙 V) (hF : Fi ≫ Fh = 𝟙 Z) (hL : Li ≫ Lh = 𝟙 W)
    (h : Sh ≫ Gh = Fh ≫ Lh) :
    Gi ≫ Si = Li ≫ Fi := by
  calc Gi ≫ Si = Li ≫ Fi ≫ Fh ≫ Lh ≫ Gi ≫ Si := by rw [reassoc_of% hF, reassoc_of% hL]
    _ = Li ≫ Fi := by rw [← reassoc_of% h, reassoc_of% hG, hS, Category.comp_id]

/-- **The inverse iterated Frobenius comparison, read against the square of two morphisms which
are the `N`-fold absolute Frobenius only up to equality.** This is
`AlgebraicGeometry.squareIter_frobeniusVectPullbackIso_hom` inverted and transported along the
two equalities; the two morphisms are kept variables so that the equalities can be discharged by
substitution. -/
lemma squareIter_inv_congr_aux (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)
    (hY : IsInCharacteristic Y p) (g : X ⟶ Y) (N : ℕ) {Pa : X ⟶ X} {Pb : Y ⟶ Y}
    (ePa : absoluteFrobeniusPow X p hX N = Pa) (ePb : absoluteFrobeniusPow Y p hY N = Pb)
    (hF : g ≫ Pb = Pa ≫ g) (E : Y.Vect) :
    (Scheme.Vect.pullback g).map ((Scheme.Vect.pullbackCongr ePb).inv.app E ≫
          (frobeniusPullbackIterIso Y p hY N).inv.app E) ≫
        (EndoColim.squareIter (frobeniusPullback Y p hY) (frobeniusPullback X p hX)
          (Scheme.Vect.pullback g) (frobeniusVectPullbackIso g p hX hY) N E).inv =
      (vectPullbackSquareIso hF).hom.app E ≫
        (Scheme.Vect.pullbackCongr ePa).inv.app ((Scheme.Vect.pullback g).obj E) ≫
          (frobeniusPullbackIterIso X p hX N).inv.app ((Scheme.Vect.pullback g).obj E) := by
  subst ePa
  subst ePb
  have hL : (vectPullbackSquareIso hF).hom.app E ≫
      (vectPullbackSquareIso (absoluteFrobeniusPow_naturality g p hX hY N)).hom.app E = 𝟙 _ := by
    rw [← vectPullbackSquareIso_inv_app_eq_symm
      (absoluteFrobeniusPow_naturality g p hX hY N) hF, Iso.inv_hom_id_app]
  have hG : (Scheme.Vect.pullback g).map ((frobeniusPullbackIterIso Y p hY N).hom.app E) ≫
      (Scheme.Vect.pullback g).map ((frobeniusPullbackIterIso Y p hY N).inv.app E) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  have hS : (EndoColim.squareIter (frobeniusPullback Y p hY) (frobeniusPullback X p hX)
          (Scheme.Vect.pullback g) (frobeniusVectPullbackIso g p hX hY) N E).hom ≫
        (EndoColim.squareIter (frobeniusPullback Y p hY) (frobeniusPullback X p hX)
          (Scheme.Vect.pullback g) (frobeniusVectPullbackIso g p hX hY) N E).inv = 𝟙 _ :=
    Iso.hom_inv_id _
  have hFi : (frobeniusPullbackIterIso X p hX N).inv.app ((Scheme.Vect.pullback g).obj E) ≫
        (frobeniusPullbackIterIso X p hX N).hom.app ((Scheme.Vect.pullback g).obj E) = 𝟙 _ :=
    Iso.inv_hom_id_app _ _
  simp only [vectPullbackCongr_refl_inv_app, Category.id_comp]
  exact inv_step_aux _ _ _ _ _ _ _ _ hS hG hFi hL
    (squareIter_frobeniusVectPullbackIso_hom p hX hY g N E)

/-- The inverse of the affine identification of the `N`-fold Frobenius pullback, split into the
transport along `AlgebraicGeometry.specMap_eq_absoluteFrobeniusPow` and the inverse of
`AlgebraicGeometry.frobeniusPullbackIterIso`. -/
lemma frobeniusPullbackIterSpecIso_inv_app (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (hp : (p : A) = 0) (N : ℕ) (M : (Spec (CommRingCat.of A)).Vect) :
    (frobeniusPullbackIterSpecIso A p hp N).inv.app M =
      (Scheme.Vect.pullbackCongr (specMap_eq_absoluteFrobeniusPow
            (MilnorPatching.OneGeneratorFrobenius.frobeniusPow A p hp N) p N
            (isInCharacteristic_spec A p hp)
            (MilnorPatching.OneGeneratorFrobenius.frobeniusPow_apply A p hp N)).symm).inv.app M ≫
        (frobeniusPullbackIterIso (Spec (CommRingCat.of A)) p
          (isInCharacteristic_spec A p hp) N).inv.app M :=
  rfl

/-- **The `p ^ N`-power endomorphism is natural in the ring.** -/
lemma frobeniusPow_naturality {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] (p : ℕ) [Fact p.Prime]
    (h₁ : (p : R₁) = 0) (h₂ : (p : R₂) = 0) (φ : R₁ →+* R₂) (N : ℕ) :
    φ.comp (MilnorPatching.OneGeneratorFrobenius.frobeniusPow R₁ p h₁ N) =
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow R₂ p h₂ N).comp φ :=
  RingHom.ext fun a ↦ by
    simp only [RingHom.coe_comp, Function.comp_apply,
      MilnorPatching.OneGeneratorFrobenius.frobeniusPow_apply, map_pow]

/-- **The square of the two `p ^ N`-power morphisms on spectra commutes.** -/
lemma specMap_frobeniusPow_square {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂] (p : ℕ)
    [Fact p.Prime] (h₁ : (p : R₁) = 0) (h₂ : (p : R₂) = 0)
    (φ : CommRingCat.of R₂ ⟶ CommRingCat.of R₁) (N : ℕ) :
    Spec.map φ ≫ Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow R₂ p h₂ N)) =
      Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow R₁ p h₁ N)) ≫ Spec.map φ := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (frobeniusPow_naturality p h₂ h₁ φ.hom N))

/-- **The inverse iterated Frobenius comparison on an affine leg is the comparison attached to
the square of the two `p ^ N`-power morphisms.** This is the form the compatibility over the
exceptional corner consumes: it replaces the comparison
`CategoryTheory.EndoColim.squareIter` of the Frobenius pullback by the comparison
`AlgebraicGeometry.vectPullbackSquareIso` of a square of morphisms of affine schemes. -/
lemma specIter_squareIter_inv (R₁ R₂ : Type u) [CommRing R₁] [CommRing R₂] (p : ℕ)
    [Fact p.Prime] (h₁ : (p : R₁) = 0) (h₂ : (p : R₂) = 0)
    (g : Spec (CommRingCat.of R₁) ⟶ Spec (CommRingCat.of R₂)) (N : ℕ)
    (hF : g ≫ Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow R₂ p h₂ N)) =
        Spec.map (CommRingCat.ofHom
          (MilnorPatching.OneGeneratorFrobenius.frobeniusPow R₁ p h₁ N)) ≫ g)
    (E : (Spec (CommRingCat.of R₂)).Vect) :
    (Scheme.Vect.pullback g).map ((frobeniusPullbackIterSpecIso R₂ p h₂ N).inv.app E) ≫
        (EndoColim.squareIter
            (frobeniusPullback (Spec (CommRingCat.of R₂)) p (isInCharacteristic_spec R₂ p h₂))
            (frobeniusPullback (Spec (CommRingCat.of R₁)) p (isInCharacteristic_spec R₁ p h₁))
            (Scheme.Vect.pullback g)
            (frobeniusVectPullbackIso g p
              (isInCharacteristic_spec R₁ p h₁) (isInCharacteristic_spec R₂ p h₂)) N E).inv =
      (vectPullbackSquareIso hF).hom.app E ≫
        (frobeniusPullbackIterSpecIso R₁ p h₁ N).inv.app ((Scheme.Vect.pullback g).obj E) := by
  rw [frobeniusPullbackIterSpecIso_inv_app, frobeniusPullbackIterSpecIso_inv_app]
  exact squareIter_inv_congr_aux p (isInCharacteristic_spec R₁ p h₁)
    (isInCharacteristic_spec R₂ p h₂) g N
    (specMap_eq_absoluteFrobeniusPow _ p N _
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow_apply R₁ p h₁ N)).symm
    (specMap_eq_absoluteFrobeniusPow _ p N _
      (MilnorPatching.OneGeneratorFrobenius.frobeniusPow_apply R₂ p h₂ N)).symm hF E

end Frobenius

/-! ### The compatibility over the exceptional corner -/

section Corner

open MilnorPatching.OneGeneratorFrobenius

/-- **The structural isomorphism carried by `ModuleGlueing.extensionOfScalarsToPullback`** is the
transport along the commuting square, read through the two identifications of the extensions of
scalars along the two composites. -/
lemma extensionOfScalarsToPullback_obj_iso_hom {R₀ R₁ R₂ R₃ : Type u} [CommRing R₀] [CommRing R₁]
    [CommRing R₂] [CommRing R₃] (toB : R₀ →+* R₁) (toA' : R₀ →+* R₂) (BtoA : R₁ →+* R₃)
    (A'toA : R₂ →+* R₃) (comm : BtoA.comp toB = A'toA.comp toA') (M : ModuleCat.{u} R₀) :
    ((ModuleGlueing.extensionOfScalarsToPullback.{u, u, u, u, u} toB toA' BtoA A'toA
          comm).obj M).iso.hom =
      (ModuleGlueing.extendScalarsComp.{u, u, u, u} toB BtoA).inv.app M ≫
        (eqToIso (congrArg ModuleCat.extendScalars comm)).hom.app M ≫
          (ModuleGlueing.extendScalarsComp.{u, u, u, u} toA' A'toA).hom.app M :=
  rfl

end Corner

end AlgebraicGeometry

end
