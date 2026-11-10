module

public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.RingTheory.Etale.StandardEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.Sequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image of the Kummer sequence

Let `π : X ⟶ Y` be a morphism of schemes.  Inverse image along `π` on abelian sheaves of the
small étale sites carries the Kummer sequence of `Y` to a short exact sequence of abelian
sheaves on the small étale site of `X`, and this file compares that sequence with the Kummer
sequence of `X`.

On `𝐆_m` the comparison `π^{-1} 𝐆_{m,Y} ⟶ 𝐆_{m,X}` is the adjoint transpose of the direct-image
comparison `𝐆_{m,Y} ⟶ π_* 𝐆_{m,X}`, which restricts an invertible function along the projection
`V ×_Y X ⟶ V`.  It is not an isomorphism.  On `μ_n` with `n` invertible on `Y` it *is* an
isomorphism, and that is the content of the file: the underlying sheaf of sets of `μ_n` is
represented by an object of the small étale site, namely the base change to the scheme of the
standard étale algebra `A[T]/(Tⁿ - 1)` over `A = Γ(Y, 𝒪_Y)`, and base change of sites carries a
representing object to a representing object.  A comparison morphism of abelian sheaves whose
transpose matches representing elements on both sides is an isomorphism, by a Yoneda argument
run inside the category of sheaves.

The two comparisons together give a morphism from the inverse image of the Kummer sequence of
`Y` to the Kummer sequence of `X`, and hence the coboundary square: for a class
`x ∈ H^q(Y, 𝐆_m)` the restriction of its Kummer coboundary in `H^{q+1}(Y, μ_n)` is the Kummer
coboundary of its restriction, transported along the `μ_n` comparison.

## Main definitions

* `Stacks.Kummer.multiplicativeInverseImageComparison`: the comparison
  `π^{-1} 𝐆_{m,Y} ⟶ 𝐆_{m,X}`.
* `Stacks.Kummer.rootsOfUnityEtaleOver`: the étale `Y`-scheme representing `μ_n`.
* `Stacks.Kummer.rootsOfUnityInverseImageIso`: the isomorphism `π^{-1} μ_{n,Y} ≅ μ_{n,X}`.
* `Stacks.Kummer.kummerSequenceInverseImageMap`: the morphism of short complexes from the
  inverse image of the Kummer sequence of `Y` to the Kummer sequence of `X`.

## Main results

* `Stacks.Kummer.multiplicativeInverseImageComparison_app_ofUnit`: the comparison on `𝐆_m`,
  computed on a section.
* `Stacks.Kummer.rootsOfUnityInverseImageComparison_comp_rootsOfUnityι`: the comparison on `μ_n`
  is compatible with the two inclusions into `𝐆_m`, which characterises it.
* `Stacks.Kummer.rootsOfUnitySectionsEquiv`: sections of `μ_n` over an étale scheme `U` are the
  `n`-th roots of unity in `Γ(U, 𝒪_U)`.
* `Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass`: the coboundary square.

## Implementation notes

The representing object is produced by hand rather than taken from
`AlgebraicGeometry.rootsOfUnityBaseChange`, whose structure morphism is the base change of
`Spec ℤ[T]/(Tⁿ - 1) ⟶ Spec ℤ`; that morphism is not étale, so étaleness of the base change would
have to be read off from a presentation over `Γ(Y, 𝒪_Y)` anyway.  Taking the standard étale pair
`(Tⁿ - 1, 1)` over `Γ(Y, 𝒪_Y)` directly makes étaleness a base change of an étale morphism, and
`StandardEtalePair.homEquiv` supplies the universal property in the form needed.

The comparison on `μ_n` is obtained from the comparison on `𝐆_m` by the universal property of
the kernel, using that inverse image preserves kernels and that every morphism of abelian
sheaves commutes with multiplication by `n`.  Its being an isomorphism is a statement about
sheaves of sets, and the Yoneda argument needs the representing element on the source to be
carried to the representing element on the target; that is exactly the formula for the
`𝐆_m` comparison on sections, which is why the two parts cannot be separated.

## References

* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL): the Kummer sequence.
* [Stacks Project, Tag 040M](https://stacks.math.columbia.edu/tag/040M): the scheme of `n`-th
  roots of unity.
* [Stacks Project, Tag 03XB](https://stacks.math.columbia.edu/tag/03XB): functoriality of the
  small étale topos.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe t t₂ v₁ u₁ v₂ u₂ u v w

namespace Stacks.Kummer

section Yoneda

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **A presheaf identified with the morphisms into a fixed object is represented by that
object.**  The identification is given by two families of bijections to a common family of types,
one from the morphisms out of each object and one from the sections of the presheaf, together with
the compatibility that pulling a section back matches precomposition of morphisms.

Both the morphism and the factorisation are left free in the compatibility hypothesis, so that it
can be discharged for identifications whose naturality is only a propositional identity. -/
theorem isRepresentedBy_of_homEquiv {T : C → Type t₂} (F : Cᵒᵖ ⥤ Type t) (E : C)
    (c : ∀ U : C, (U ⟶ E) ≃ T U) (d : ∀ U : C, F.obj (op U) ≃ T U)
    (hcd : ∀ {U V : C} (g : V ⟶ U) (h : U ⟶ E) (k : V ⟶ E) (s : F.obj (op U)),
      k = g ≫ h → d U s = c U h → d V (F.map g.op s) = c V k) :
    F.IsRepresentedBy ((d E).symm (c E (𝟙 E))) := by
  constructor
  intro U
  have key : ∀ h : U ⟶ E, d U (F.map h.op ((d E).symm (c E (𝟙 E)))) = c U h := fun h =>
    hcd h (𝟙 E) h _ (Category.comp_id h).symm ((d E).apply_symm_apply _)
  have hfun : (fun h : U ⟶ E => F.map h.op ((d E).symm (c E (𝟙 E)))) = (d U).symm ∘ c U := by
    funext h
    exact ((d U).symm_apply_apply _).symm.trans (congrArg (d U).symm (key h))
  rw [hfun]
  exact (d U).symm.bijective.comp (c U).bijective

/-- **A comparison morphism matching representing elements is an isomorphism.**  Let `G` be a
continuous functor of sites, with inverse image `P` left adjoint to the pushforward, and let
`c : P A ⟶ B` be a morphism of abelian sheaves.  If the underlying sheaf of sets of `A` is
represented by `E` with universal element `a`, and that of `B` is represented by `G E` with
universal element the image of `a` under the transpose of `c`, then `c` is an isomorphism.

The inverse is built by Yoneda: a section of `B` over `U` is a morphism `U ⟶ G E`, which is
carried to a section of `P A` by functoriality applied to the image of `a` under the unit of
the adjunction.  That this is additive is where the hypothesis that `G` preserves the binary
product `E × E` is used: addition on sections of a represented sheaf is induced by a morphism
out of `E × E`, and a section of `B` over `U` must be pulled back from `G (E × E)`. -/
theorem isIso_of_isRepresentedBy_transpose (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsContinuous J K]
    {P : Sheaf J AddCommGrpCat.{t} ⥤ Sheaf K AddCommGrpCat.{t}}
    (adj : P ⊣ G.sheafPushforwardContinuous AddCommGrpCat.{t} J K)
    (A : Sheaf J AddCommGrpCat.{t}) (B : Sheaf K AddCommGrpCat.{t}) (c : P.obj A ⟶ B)
    (E : C) [HasBinaryProduct E E] [PreservesLimit (pair E E) G]
    (a : ToType (A.obj.obj (op E)))
    (ha : (A.obj ⋙ CategoryTheory.forget AddCommGrpCat).IsRepresentedBy a)
    (hb : (B.obj ⋙ CategoryTheory.forget AddCommGrpCat).IsRepresentedBy
      ((adj.homEquiv A B c).hom.app (op E) a)) :
    IsIso c := by
  let H := P.obj A
  let α : A.obj ⟶ G.op ⋙ B.obj := (adj.homEquiv A B c).hom
  let η : A.obj ⟶ G.op ⋙ H.obj := (adj.unit.app A).hom
  let b : ToType (B.obj.obj (op (G.obj E))) := α.app (op E) a
  let q (U : D) : ToType (B.obj.obj (op U)) → (U ⟶ G.obj E) :=
    (Equiv.ofBijective _ hb.map_bijective).symm
  have hq (U : D) (s : ToType (B.obj.obj (op U))) : B.obj.map (q U s).op b = s :=
    (Equiv.ofBijective _ hb.map_bijective).apply_symm_apply s
  have hq' (U : D) (g : U ⟶ G.obj E) : q U (B.obj.map g.op b) = g :=
    (Equiv.ofBijective _ hb.map_bijective).symm_apply_apply g
  let β (U : D) (s : ToType (B.obj.obj (op U))) : ToType (H.obj.obj (op U)) :=
    H.obj.map (q U s).op (η.app (op E) a)
  have hβ (U : D) (g : U ⟶ G.obj E) :
      β U (B.obj.map g.op b) = H.obj.map g.op (η.app (op E) a) := by
    simp only [β, hq']
  have hn {U V : D} (g : V ⟶ U) (s : ToType (B.obj.obj (op U))) :
      β V (B.obj.map g.op s) = H.obj.map g.op (β U s) := by
    have h : q V (B.obj.map g.op s) = g ≫ q U s := by
      apply hb.map_bijective.injective
      change B.obj.map _ b = B.obj.map _ b
      rw [hq, op_comp, B.obj.map_comp, AddCommGrpCat.comp_apply, hq]
    dsimp only [β]
    rw [h, op_comp, H.obj.map_comp, AddCommGrpCat.comp_apply]
  have hα (U : C) (s : ToType (A.obj.obj (op U))) :
      β (G.obj U) (α.app (op U) s) = η.app (op U) s := by
    obtain ⟨g, rfl⟩ := ha.map_bijective.surjective s
    have hnα := ConcreteCategory.congr_hom (α.naturality g.op) a
    have hnη := ConcreteCategory.congr_hom (η.naturality g.op) a
    change α.app (op U) (A.obj.map g.op a) = B.obj.map (G.map g).op b at hnα
    change β (G.obj U) (α.app (op U) (A.obj.map g.op a)) = η.app (op U) (A.obj.map g.op a)
    rw [hnα, hβ]
    exact hnη.symm
  have hadd (U : D) (s t : ToType (B.obj.obj (op U))) : β U (s + t) = β U s + β U t := by
    let V := E ⨯ E
    let s₀ := A.obj.map (prod.fst : V ⟶ E).op a
    let t₀ := A.obj.map (prod.snd : V ⟶ E).op a
    let g : U ⟶ G.obj V :=
      prod.lift (q U s) (q U t) ≫ (PreservesLimitPair.iso G E E).inv
    have hg₁ : g ≫ G.map (prod.fst : V ⟶ E) = q U s := by simp [g]
    have hg₂ : g ≫ G.map (prod.snd : V ⟶ E) = q U t := by simp [g]
    have hproj (p : V ⟶ E) (s' : ToType (B.obj.obj (op U))) (hp : g ≫ G.map p = q U s') :
        B.obj.map g.op (α.app (op V) (A.obj.map p.op a)) = s' := by
      have he := ConcreteCategory.congr_hom (α.naturality p.op) a
      change α.app (op V) (A.obj.map p.op a) = B.obj.map (G.map p).op b at he
      rw [he, ← AddCommGrpCat.comp_apply, ← B.obj.map_comp, ← op_comp, hp, hq]
    have hs : B.obj.map g.op (α.app (op V) s₀) = s := hproj _ _ hg₁
    have ht : B.obj.map g.op (α.app (op V) t₀) = t := hproj _ _ hg₂
    rw [← hs, ← ht, ← map_add, ← map_add, hn, hα, map_add, map_add,
      ← hα V s₀, ← hα V t₀, ← hn, ← hn]
  let d : B ⟶ H :=
    ⟨{ app := fun U => AddCommGrpCat.ofHom
        { toFun := β U.unop
          map_zero' := by
            simpa using (congrArg (fun x => x - β U.unop 0) (hadd U.unop 0 0)).symm
          map_add' := hadd U.unop }
       naturality := by
         intro U V g
         ext s
         exact hn g.unop s }⟩
  have hdc : d ≫ c = 𝟙 B := by
    ext U s
    change c.hom.app U (H.obj.map (q U.unop s).op (η.app (op E) a)) = s
    rw [← AddCommGrpCat.comp_apply, c.hom.naturality]
    exact hq U.unop s
  have hcd : c ≫ d = 𝟙 H := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_right]
    ext U s
    exact hα U.unop s
  exact ⟨⟨d, hcd, hdc⟩⟩

/-- The morphism of `X`-schemes corresponding to a morphism into a base change, read on
underlying schemes: it is the given morphism followed by the base-change projection. -/
theorem mapPullbackAdj_homEquiv_symm_left {C : Type u₁} [Category.{v₁} C] {S T : C} (f : S ⟶ T)
    [Limits.HasPullbacksAlong f] {W : CategoryTheory.Over S}
    {A : CategoryTheory.Over T} (v : W ⟶ (CategoryTheory.Over.pullback f).obj A) :
    (((CategoryTheory.Over.mapPullbackAdj f).homEquiv W A).symm v).left =
      v.left ≫ pullback.fst A.hom f := by
  rw [Adjunction.homEquiv_counit]
  simp

end Yoneda

section MultiplicativeComparison

variable {X Y : Scheme.{u}} (π : X ⟶ Y)

/-- **The comparison `π^{-1} 𝐆_{m,Y} ⟶ 𝐆_{m,X}`** for a morphism of schemes `π : X ⟶ Y`: the
adjoint transpose of `Stacks.EtaleCohomology.multiplicativeDirectImageComparison`, which on
sections over an étale `Y`-scheme `V` restricts an invertible global function along the
projection `V ×_Y X ⟶ V`. -/
def multiplicativeInverseImageComparison :
    (etaleAbelianInverseImage.{u, v} π).obj (multiplicativeSheaf.{u, v} Y) ⟶
      multiplicativeSheaf.{u, v} X :=
  ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv
    (multiplicativeSheaf.{u, v} Y) (multiplicativeSheaf.{u, v} X)).symm
    (multiplicativeDirectImageComparison.{u, v} π)

/-- The transpose of the comparison on `𝐆_m` is the direct-image comparison. -/
theorem multiplicativeInverseImageComparison_transpose :
    (etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv
        (multiplicativeSheaf.{u, v} Y) (multiplicativeSheaf.{u, v} X)
        (multiplicativeInverseImageComparison.{u, v} π) =
      multiplicativeDirectImageComparison.{u, v} π :=
  Equiv.apply_symm_apply _ _

/-- **The comparison on `𝐆_m`, computed on a section.**  An invertible global function `x` on an
étale `Y`-scheme `V`, viewed as a section of `π^{-1} 𝐆_{m,Y}` over `V ×_Y X` through the unit of
the adjunction, is carried to its pullback along the projection `V ×_Y X ⟶ V`. -/
theorem multiplicativeInverseImageComparison_app_ofUnit (V : Y.Etale) (x : (Γ(V.left, ⊤))ˣ) :
    (multiplicativeInverseImageComparison.{u, v} π).hom.app
        (op ((smallEtaleBaseChange π).obj V))
        (((etaleAbelianInverseImageDirectImageAdj.{u, v} π).unit.app
          (multiplicativeSheaf.{u, v} Y)).hom.app (op V) (ofUnit x)) =
      ofUnit (U := (smallEtaleBaseChange π).obj V)
        (Units.map (pullback.fst V.hom π).appTop.hom.toMonoidHom x) := by
  have h := multiplicativeInverseImageComparison_transpose.{u, v} π
  rw [Adjunction.homEquiv_unit] at h
  have h2 := congrArg (fun φ : multiplicativeSheaf.{u, v} Y ⟶
      (etaleAbelianDirectImage.{u, v} π).obj (multiplicativeSheaf.{u, v} X) =>
    φ.hom.app (op V) (ofUnit.{u, v} x)) h
  exact h2.trans (multiplicativeDirectImageComparison_app_ofUnit.{u, v} π V x)

end MultiplicativeComparison

section RootsRepresentation

open Polynomial

/-- The standard étale pair `(Tⁿ - 1, 1)` over a ring in which `n` is invertible.  Its étale
algebra is `R[T]/(Tⁿ - 1)`, and the maps out of it to an `R`-algebra `S` are the `n`-th roots of
unity in `S`.  Invertibility of `n` is exactly what makes the derivative `n Tⁿ⁻¹` invertible
modulo `Tⁿ - 1`. -/
def rootsOfUnityPair (R : Type u) [CommRing R] (n : ℕ) (hn : IsUnit ((n : ℕ) : R)) :
    StandardEtalePair R where
  f := X ^ n - 1
  monic_f := by
    by_cases h : n = 0
    · subst h
      have : Subsingleton R := subsingleton_of_zero_eq_one
        (isUnit_zero_iff.mp (by simpa using hn))
      exact Subsingleton.elim _ _
    · exact monic_X_pow_sub_C (1 : R) h
  g := 1
  cond := by
    classical
    by_cases h : n = 0
    · subst h
      have : Subsingleton R := subsingleton_of_zero_eq_one
        (isUnit_zero_iff.mp (by simpa using hn))
      exact ⟨0, 0, 0, Subsingleton.elim _ _⟩
    obtain ⟨a, ha⟩ := hn
    refine ⟨C (↑(a⁻¹) : R) * X, -1, 0, ?_⟩
    rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, ← ha]
    have hexp : X ^ (n - 1) * X = (X ^ n : R[X]) := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)]
    calc
      C (↑a) * X ^ (n - 1) * (C (↑(a⁻¹)) * X) + (X ^ n - 1) * -1 =
          C ((a : R) * ↑(a⁻¹)) * (X ^ (n - 1) * X) - (X ^ n - 1) := by
        rw [map_mul]
        ring
      _ = 1 := by simp [hexp]

/-- A ring element whose `n`-th power is one is a unit, with inverse its `(n-1)`-st power.
Invertibility of `n` is used only to rule out `n = 0` in a nonzero ring. -/
def unitOfPowEqOne {R : Type u} [CommRing R] (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
    (x : R) (hx : x ^ n = 1) : Rˣ where
  val := x
  inv := x ^ (n - 1)
  val_inv := by
    by_cases h : n = 0
    · subst h
      have : Subsingleton R := subsingleton_of_zero_eq_one
        (isUnit_zero_iff.mp (by simpa using hn))
      exact Subsingleton.elim _ _
    · rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h), hx]
  inv_val := by
    by_cases h : n = 0
    · subst h
      have : Subsingleton R := subsingleton_of_zero_eq_one
        (isUnit_zero_iff.mp (by simpa using hn))
      exact Subsingleton.elim _ _
    · rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h), hx]

/-- **The universal property of `R[T]/(Tⁿ - 1)`**: its `R`-algebra maps to `S` are the `n`-th
roots of unity in the unit group of `S`. -/
def rootsOfUnityPairHomEquiv (R : Type u) [CommRing R] (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
    (S : Type u) [CommRing S] [Algebra R S] :
    ((rootsOfUnityPair R n hn).Ring →ₐ[R] S) ≃ {x : Sˣ // x ^ n = 1} :=
  (rootsOfUnityPair R n hn).homEquiv.trans
    { toFun := fun ⟨x, hx⟩ =>
        ⟨unitOfPowEqOne n (by simpa using hn.map (algebraMap R S)) x
          (by simpa [rootsOfUnityPair, sub_eq_zero] using hx.1),
          Units.ext (by
            simpa [unitOfPowEqOne, rootsOfUnityPair, sub_eq_zero] using hx.1)⟩
      invFun := fun ⟨x, hx⟩ => ⟨x.val,
        ⟨by simpa [rootsOfUnityPair, sub_eq_zero] using congrArg Units.val hx,
          by simp [rootsOfUnityPair]⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext (Units.ext rfl) }

/-- The root of unity attached to an algebra map out of `R[T]/(Tⁿ - 1)` is the image of `T`. -/
theorem rootsOfUnityPairHomEquiv_val (R : Type u) [CommRing R] (n : ℕ)
    (hn : IsUnit ((n : ℕ) : R)) (S : Type u) [CommRing S] [Algebra R S]
    (g : (rootsOfUnityPair R n hn).Ring →ₐ[R] S) :
    ((rootsOfUnityPairHomEquiv R n hn S g).1 : S) = g (rootsOfUnityPair R n hn).X :=
  rfl

/-- Morphisms from a scheme to an affine scheme are ring maps out of its coordinate ring, the
`Γ-Spec` adjunction read on global sections. -/
@[ega "I 2.2.4"]
def schemeHomSpecEquiv (T : Scheme.{u}) (A : Type u) [CommRing A] :
    (T ⟶ Spec (.of A)) ≃ (A →+* Γ(T, ⊤)) where
  toFun g := ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom
  invFun φ := T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)
  left_inv g := by
    apply ext_to_Spec
    simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      Scheme.ΓSpecIso_naturality, CommRingCat.ofHom_hom]
    exact Iso.inv_hom_id_assoc _ _
  right_inv φ := by
    change ((Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec.map (CommRingCat.ofHom φ)).appTop ≫ T.toSpecΓ.appTop).hom = φ
    rw [Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rfl

/-- Composing with `Spec` of a ring map precomposes the corresponding ring map. -/
theorem schemeHomSpecEquiv_comp (T : Scheme.{u}) {A R : Type u} [CommRing A] [CommRing R]
    (φ : R →+* A) (g : T ⟶ Spec (.of A)) :
    schemeHomSpecEquiv T R (g ≫ Spec.map (CommRingCat.ofHom φ)) =
      (schemeHomSpecEquiv T A g).comp φ := by
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ _).hom = _
  rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- Morphisms of `Spec Γ(Y, 𝒪_Y)`-schemes from a `Y`-scheme to the spectrum of a
`Γ(Y, 𝒪_Y)`-algebra `A` are the `Γ(Y, 𝒪_Y)`-algebra maps from `A` to its global functions. -/
def overSpecHomEquiv (Y : Scheme.{u}) (A : Type u) [CommRing A] [Algebra Γ(Y, ⊤) A]
    (U : CategoryTheory.Over Y) :
    letI := U.hom.appTop.hom.toAlgebra
    (((CategoryTheory.Over.map Y.toSpecΓ).obj U) ⟶
      CategoryTheory.Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) A)))) ≃
      (A →ₐ[Γ(Y, ⊤)] Γ(U.left, ⊤)) := by
  letI := U.hom.appTop.hom.toAlgebra
  refine {
    toFun := fun g => {
      __ := schemeHomSpecEquiv U.left A g.left
      commutes' := ?_ }
    invFun := fun φ => CategoryTheory.Over.homMk
      ((schemeHomSpecEquiv U.left A).symm φ.toRingHom) ?_
    left_inv := ?_
    right_inv := ?_ }
  · intro r
    have hg := congrArg (schemeHomSpecEquiv U.left Γ(Y, ⊤)) (CategoryTheory.Over.w g)
    dsimp only [CategoryTheory.Over.mk_hom, CategoryTheory.Over.map_obj_hom] at hg
    rw [schemeHomSpecEquiv_comp] at hg
    have hy : schemeHomSpecEquiv U.left Γ(Y, ⊤) (U.hom ≫ Y.toSpecΓ) = U.hom.appTop.hom := by
      change ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ (U.hom ≫ Y.toSpecΓ).appTop).hom = _
      rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
    rw [hy] at hg
    exact congrArg (fun ψ => ψ r) hg
  · apply (schemeHomSpecEquiv U.left Γ(Y, ⊤)).injective
    dsimp only [CategoryTheory.Over.mk_hom, CategoryTheory.Over.map_obj_hom]
    rw [schemeHomSpecEquiv_comp, Equiv.apply_symm_apply]
    change φ.toRingHom.comp (algebraMap Γ(Y, ⊤) A) =
      ((Scheme.ΓSpecIso Γ(Y, ⊤)).inv ≫ (U.hom ≫ Y.toSpecΓ).appTop).hom
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
    exact φ.comp_algebraMap
  · exact fun g => CategoryTheory.Over.OverMorphism.ext
      ((schemeHomSpecEquiv U.left A).symm_apply_apply g.left)
  · exact fun φ => AlgHom.toRingHom_injective
      ((schemeHomSpecEquiv U.left A).apply_symm_apply φ.toRingHom)

variable (Y : Scheme.{u}) (n : ℕ) (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤)))

/-- **The scheme of `n`-th roots of unity over `Y`**, as a `Y`-scheme: the base change along
`Y ⟶ Spec Γ(Y, 𝒪_Y)` of the spectrum of the standard étale algebra
`Γ(Y, 𝒪_Y)[T]/(Tⁿ - 1)`. -/
def rootsOfUnityEtaleOver : CategoryTheory.Over Y :=
  (CategoryTheory.Over.pullback Y.toSpecΓ).obj
    (CategoryTheory.Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Y, ⊤) (rootsOfUnityPair Γ(Y, ⊤) n hn).Ring))))

/-- The scheme of `n`-th roots of unity is étale over `Y`: it is the base change of an étale
morphism of affine schemes. -/
instance rootsOfUnityEtaleOver_etale : Etale (rootsOfUnityEtaleOver Y n hn).hom := by
  have : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(Y, ⊤) (rootsOfUnityPair Γ(Y, ⊤) n hn).Ring))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  change Etale (pullback.snd (Spec.map (CommRingCat.ofHom
    (algebraMap Γ(Y, ⊤) (rootsOfUnityPair Γ(Y, ⊤) n hn).Ring))) Y.toSpecΓ)
  infer_instance

/-- **The universal property of the scheme of `n`-th roots of unity over `Y`**: morphisms of
`Y`-schemes into it from an arbitrary `Y`-scheme `U` are the `n`-th roots of unity in
`Γ(U, 𝒪_U)`. -/
def rootsOfUnityEtaleOverHomEquiv (U : CategoryTheory.Over Y) :
    (U ⟶ rootsOfUnityEtaleOver Y n hn) ≃ {x : (Γ(U.left, ⊤))ˣ // x ^ n = 1} := by
  letI := U.hom.appTop.hom.toAlgebra
  exact ((CategoryTheory.Over.mapPullbackAdj Y.toSpecΓ).homEquiv U _).symm.trans
    ((overSpecHomEquiv Y (rootsOfUnityPair Γ(Y, ⊤) n hn).Ring U).trans
      (rootsOfUnityPairHomEquiv Γ(Y, ⊤) n hn Γ(U.left, ⊤)))

/-- The root of unity attached to a morphism into the scheme of `n`-th roots of unity is the
pullback of the coordinate `T` along it. -/
theorem rootsOfUnityEtaleOverHomEquiv_val (U : CategoryTheory.Over Y)
    (g : U ⟶ rootsOfUnityEtaleOver Y n hn) :
    ((rootsOfUnityEtaleOverHomEquiv Y n hn U g).1 : Γ(U.left, ⊤)) =
      (((Scheme.ΓSpecIso (.of (rootsOfUnityPair Γ(Y, ⊤) n hn).Ring)).inv ≫
        (g.left ≫ pullback.fst _ Y.toSpecΓ).appTop)
          (rootsOfUnityPair Γ(Y, ⊤) n hn).X) :=
  rfl

/-- **Naturality of the universal property of the scheme of `n`-th roots of unity.**  If the
underlying morphism of schemes of `k` factors as `g` followed by that of `h`, then the root of
unity attached to `k` is the pullback along `g` of the one attached to `h`.

The hypothesis is on the underlying morphisms of schemes rather than on `k` itself, so that the
lemma applies to morphisms produced by an adjunction, whose factorisation is only a propositional
identity. -/
theorem rootsOfUnityEtaleOverHomEquiv_map_left {U V : CategoryTheory.Over Y}
    (g : V ⟶ U) (h : U ⟶ rootsOfUnityEtaleOver Y n hn)
    (k : V ⟶ rootsOfUnityEtaleOver Y n hn) (hk : k.left = g.left ≫ h.left) :
    (rootsOfUnityEtaleOverHomEquiv Y n hn V k).1 =
      Units.map g.left.appTop.hom.toMonoidHom
        (rootsOfUnityEtaleOverHomEquiv Y n hn U h).1 := by
  apply Units.ext
  rw [Units.coe_map, rootsOfUnityEtaleOverHomEquiv_val, rootsOfUnityEtaleOverHomEquiv_val, hk]
  rfl

/-- The universal property of the scheme of `n`-th roots of unity is natural: precomposing a
morphism pulls the corresponding root of unity back. -/
theorem rootsOfUnityEtaleOverHomEquiv_naturality {U V : CategoryTheory.Over Y}
    (g : V ⟶ U) (h : U ⟶ rootsOfUnityEtaleOver Y n hn) :
    (rootsOfUnityEtaleOverHomEquiv Y n hn V (g ≫ h)).1 =
      Units.map g.left.appTop.hom.toMonoidHom
        (rootsOfUnityEtaleOverHomEquiv Y n hn U h).1 :=
  rootsOfUnityEtaleOverHomEquiv_map_left Y n hn g h (g ≫ h) rfl

end RootsRepresentation

section RootsSections

variable (X : Scheme.{u}) (n : ℕ)

/-- The `n`-th root of unity underlying a section of `μ_n` over an étale scheme: its image under
the inclusion `μ_n ⟶ 𝐆_m`, which is an invertible global function with `n`-th power one. -/
def rootsOfUnitySection (U : X.Etaleᵒᵖ)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj U)) :
    {x : (Γ(U.unop.left, ⊤))ˣ // x ^ n = 1} :=
  ⟨Additive.toMul (((rootsOfUnityι.{u, v} X n).hom.app U s).down),
    pow_eq_one_of_rootsOfUnitySheaf.{u, v} X n U.unop s _ rfl⟩

/-- The inclusion `μ_n ⟶ 𝐆_m` on sections, by construction of
`Stacks.Kummer.rootsOfUnitySection`. -/
theorem rootsOfUnityι_app_eq_ofUnit (U : X.Etaleᵒᵖ)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj U)) :
    (rootsOfUnityι.{u, v} X n).hom.app U s = ofUnit (rootsOfUnitySection.{u, v} X n U s).1 :=
  rfl

/-- **Sections of `μ_n` over an étale scheme `U` are exactly the `n`-th roots of unity in
`Γ(U, 𝒪_U)`.**  Kernels of abelian sheaves are computed section by section, because evaluation
at an object of the site preserves limits, and the group-theoretic kernel of the `n`-th power
map is the set of `n`-th roots of unity. -/
@[sga "5 VI 3.2" "partial"]
theorem rootsOfUnitySection_bijective (U : X.Etaleᵒᵖ) :
    Function.Bijective (rootsOfUnitySection.{u, v} X n U) := by
  let ev := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⋙
    (evaluation X.Etaleᵒᵖ AddCommGrpCat.{max (u + 1) v}).obj U
  let p := powMap.{u, v} X n
  let e := PreservesKernel.iso ev p ≪≫ AddCommGrpCat.kernelIsoKer (ev.map p)
  have h : e.hom ≫ AddCommGrpCat.ofHom (ev.map p).hom.ker.subtype = ev.map (kernel.ι p) := by
    rw [show e.hom = (PreservesKernel.iso ev p).hom ≫
      (AddCommGrpCat.kernelIsoKer (ev.map p)).hom from rfl, Category.assoc,
      AddCommGrpCat.kernelIsoKer_hom_comp_subtype, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
  let k : ToType (AddCommGrpCat.of (ev.map p).hom.ker) ≃
      {x : (Γ(U.unop.left, ⊤))ˣ // x ^ n = 1} :=
    { toFun := fun z => ⟨Additive.toMul z.val.down, by
        refine ofUnit_injective.{u, v} (U := U.unop) ?_
        rw [ofUnit_one, ← powMap_app_ofUnit X n U.unop]
        exact AddMonoidHom.mem_ker.mp z.property⟩
      invFun := fun x => ⟨ofUnit.{u, v} x.val, by
        rw [AddMonoidHom.mem_ker]
        change (powMap.{u, v} X n).hom.app U (ofUnit x.val) = 0
        rw [powMap_app_ofUnit, x.property, ofUnit_one]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfun : rootsOfUnitySection.{u, v} X n U =
      k ∘ (fun s => (ConcreteCategory.hom e.hom) s) := by
    funext s
    refine Subtype.ext (ofUnit_injective.{u, v} (X := X) (U := U.unop) ?_)
    rw [← rootsOfUnityι_app_eq_ofUnit.{u, v} X n U s]
    exact (ConcreteCategory.congr_hom h s).symm
  rw [hfun]
  exact k.bijective.comp (ConcreteCategory.bijective_of_isIso e.hom)

/-- Sections of `μ_n` over an étale scheme `U`, identified with the `n`-th roots of unity in
`Γ(U, 𝒪_U)`. -/
noncomputable def rootsOfUnitySectionsEquiv (U : X.Etaleᵒᵖ) :
    ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj U) ≃
      {x : (Γ(U.unop.left, ⊤))ˣ // x ^ n = 1} :=
  Equiv.ofBijective _ (rootsOfUnitySection_bijective.{u, v} X n U)

/-- The equivalence `rootsOfUnitySectionsEquiv` sends a section of `μ_n` to its underlying `n`-th
root of unity `rootsOfUnitySection`. -/
@[simp]
theorem rootsOfUnitySectionsEquiv_apply (U : X.Etaleᵒᵖ)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj U)) :
    rootsOfUnitySectionsEquiv.{u, v} X n U s = rootsOfUnitySection.{u, v} X n U s :=
  rfl

/-- The `n`-th root of unity underlying a section of `μ_n` is natural: restricting a section
pulls the root of unity back. -/
theorem rootsOfUnitySection_naturality {U V : X.Etale} (g : V ⟶ U)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj (op U))) :
    (rootsOfUnitySection.{u, v} X n (op V)
        ((rootsOfUnitySheaf.{u, v} X n).obj.map g.op s)).1 =
      Units.map g.left.appTop.hom (rootsOfUnitySection.{u, v} X n (op U) s).1 := by
  refine ofUnit_injective.{u, v} ?_
  calc ofUnit (rootsOfUnitySection.{u, v} X n (op V)
          ((rootsOfUnitySheaf.{u, v} X n).obj.map g.op s)).1
      = (rootsOfUnityι.{u, v} X n).hom.app (op V)
          ((rootsOfUnitySheaf.{u, v} X n).obj.map g.op s) :=
        (rootsOfUnityι_app_eq_ofUnit.{u, v} X n (op V) _).symm
    _ = (multiplicativeSheaf.{u, v} X).obj.map g.op
          ((rootsOfUnityι.{u, v} X n).hom.app (op U) s) :=
        ConcreteCategory.congr_hom ((rootsOfUnityι.{u, v} X n).hom.naturality g.op) s
    _ = (multiplicativeSheaf.{u, v} X).obj.map g.op
          (ofUnit (rootsOfUnitySection.{u, v} X n (op U) s).1) :=
        congrArg _ (rootsOfUnityι_app_eq_ofUnit.{u, v} X n (op U) s)
    _ = ofUnit (Units.map g.left.appTop.hom (rootsOfUnitySection.{u, v} X n (op U) s).1) :=
        map_ofUnit g _

end RootsSections

section RootsComparison

/-- **The scheme of `n`-th roots of unity over `Y`, as an object of the small étale site.** -/
def rootsOfUnityEtaleObj (Y : Scheme.{u}) (n : ℕ) (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) : Y.Etale :=
  Scheme.Etale.mk (rootsOfUnityEtaleOver Y n hn).hom

/-- **The universal property of the scheme of `n`-th roots of unity, on the small étale site of
`Y`.** -/
def rootsOfUnityEtaleHomEquiv (Y : Scheme.{u}) (n : ℕ) (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    (U : Y.Etale) :
    (U ⟶ rootsOfUnityEtaleObj Y n hn) ≃ {x : (Γ(U.left, ⊤))ˣ // x ^ n = 1} :=
  (Scheme.Etale.forgetFullyFaithful Y).homEquiv.trans
    (rootsOfUnityEtaleOverHomEquiv Y n hn ((Scheme.Etale.forget Y).obj U))

/-- Naturality of the universal property on the small étale site. -/
theorem rootsOfUnityEtaleHomEquiv_naturality (Y : Scheme.{u}) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) {U V : Y.Etale} (g : V ⟶ U)
    (h : U ⟶ rootsOfUnityEtaleObj Y n hn) :
    (rootsOfUnityEtaleHomEquiv Y n hn V (g ≫ h)).1 =
      Units.map g.left.appTop.hom.toMonoidHom (rootsOfUnityEtaleHomEquiv Y n hn U h).1 :=
  rootsOfUnityEtaleOverHomEquiv_map_left Y n hn ((Scheme.Etale.forget Y).map g)
    ((Scheme.Etale.forget Y).map h) ((Scheme.Etale.forget Y).map (g ≫ h)) rfl

/-- **The universal property of the scheme of `n`-th roots of unity, on the small étale site of
`X` after base change along `π`.**  Morphisms of étale `X`-schemes into the base change are, by
the base-change adjunction, morphisms of `Y`-schemes into the scheme of roots of unity over
`Y`. -/
def rootsOfUnityEtaleBaseChangeHomEquiv {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) (U : X.Etale) :
    (U ⟶ (smallEtaleBaseChange π).obj (rootsOfUnityEtaleObj Y n hn)) ≃
      {x : (Γ(U.left, ⊤))ˣ // x ^ n = 1} :=
  (Scheme.Etale.forgetFullyFaithful X).homEquiv.trans
    (((CategoryTheory.Over.mapPullbackAdj π).homEquiv ((Scheme.Etale.forget X).obj U)
        (rootsOfUnityEtaleOver Y n hn)).symm.trans
      (rootsOfUnityEtaleOverHomEquiv Y n hn
        ((CategoryTheory.Over.map π).obj ((Scheme.Etale.forget X).obj U))))

/-- Naturality of the universal property after base change. -/
theorem rootsOfUnityEtaleBaseChangeHomEquiv_naturality {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) {U V : X.Etale} (g : V ⟶ U)
    (h : U ⟶ (smallEtaleBaseChange π).obj (rootsOfUnityEtaleObj Y n hn)) :
    (rootsOfUnityEtaleBaseChangeHomEquiv π n hn V (g ≫ h)).1 =
      Units.map g.left.appTop.hom.toMonoidHom
        (rootsOfUnityEtaleBaseChangeHomEquiv π n hn U h).1 := by
  refine rootsOfUnityEtaleOverHomEquiv_map_left Y n hn
    ((CategoryTheory.Over.map π).map ((Scheme.Etale.forget X).map g))
    (((CategoryTheory.Over.mapPullbackAdj π).homEquiv ((Scheme.Etale.forget X).obj U)
      (rootsOfUnityEtaleOver Y n hn)).symm ((Scheme.Etale.forget X).map h)) _ ?_
  refine (mapPullbackAdj_homEquiv_symm_left π _).trans
    ((Category.assoc _ _ _).trans (congrArg (fun z => g.left ≫ z) ?_))
  exact (mapPullbackAdj_homEquiv_symm_left π ((Scheme.Etale.forget X).map h)).symm

/-- The identity of the base change corresponds to the pullback of the universal root of unity
along the base-change projection. -/
theorem rootsOfUnityEtaleBaseChangeHomEquiv_id {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    (rootsOfUnityEtaleBaseChangeHomEquiv π n hn
        ((smallEtaleBaseChange π).obj (rootsOfUnityEtaleObj Y n hn)) (𝟙 _)).1 =
      Units.map (pullback.fst (rootsOfUnityEtaleObj Y n hn).hom π).appTop.hom.toMonoidHom
        (rootsOfUnityEtaleHomEquiv Y n hn (rootsOfUnityEtaleObj Y n hn) (𝟙 _)).1 := by
  refine rootsOfUnityEtaleOverHomEquiv_map_left Y n hn
    (CategoryTheory.Over.homMk (U := (CategoryTheory.Over.map π).obj
        ((Scheme.Etale.forget X).obj
          ((smallEtaleBaseChange π).obj (rootsOfUnityEtaleObj Y n hn))))
      (V := (Scheme.Etale.forget Y).obj (rootsOfUnityEtaleObj Y n hn))
      (pullback.fst (rootsOfUnityEtaleObj Y n hn).hom π) pullback.condition)
    ((Scheme.Etale.forget Y).map (𝟙 (rootsOfUnityEtaleObj Y n hn))) _ ?_
  exact (mapPullbackAdj_homEquiv_symm_left π _).trans
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- The universal `n`-th root of unity, as a section of `μ_n` over the scheme of `n`-th roots of
unity over `Y`. -/
def rootsOfUnityUniversalSection (Y : Scheme.{u}) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    ToType ((rootsOfUnitySheaf.{u, v} Y n).obj.obj (op (rootsOfUnityEtaleObj Y n hn))) :=
  (rootsOfUnitySectionsEquiv.{u, v} Y n (op (rootsOfUnityEtaleObj Y n hn))).symm
    (rootsOfUnityEtaleHomEquiv Y n hn (rootsOfUnityEtaleObj Y n hn) (𝟙 _))

/-- A family of bijections from the morphisms into an étale scheme `E` to the `n`-th roots of unity,
natural in the source, makes `μ_n` represented by `E`. -/
private theorem isRepresentedBy_rootsOfUnitySheaf_of_naturality (X : Scheme.{u}) (n : ℕ)
    (E : X.Etale) (e : ∀ U : X.Etale, (U ⟶ E) ≃ {x : (Γ(U.left, ⊤))ˣ // x ^ n = 1})
    (he : ∀ {U V : X.Etale} (g : V ⟶ U) (h : U ⟶ E),
      (e V (g ≫ h)).1 = Units.map g.left.appTop.hom.toMonoidHom (e U h).1) :
    ((rootsOfUnitySheaf.{u, v} X n).obj ⋙
      CategoryTheory.forget AddCommGrpCat).IsRepresentedBy
      ((rootsOfUnitySectionsEquiv.{u, v} X n (op E)).symm (e E (𝟙 E))) :=
  isRepresentedBy_of_homEquiv (T := fun U : X.Etale => {x : (Γ(U.left, ⊤))ˣ // x ^ n = 1})
    ((rootsOfUnitySheaf.{u, v} X n).obj ⋙ CategoryTheory.forget AddCommGrpCat) E e
    (fun U => rootsOfUnitySectionsEquiv.{u, v} X n (op U))
    (fun {_ V} g h _ s hk hs => Subtype.ext
      ((rootsOfUnitySection_naturality.{u, v} X n g s).trans
        ((congrArg (Units.map g.left.appTop.hom.toMonoidHom) (congrArg Subtype.val hs)).trans
          ((he g h).symm.trans (congrArg (fun z => (e V z).1) hk.symm)))))

/-- **`μ_n` on the small étale site of `Y` is represented by the scheme of `n`-th roots of unity
over `Y`**, with universal element the universal root of unity. -/
theorem isRepresentedBy_rootsOfUnityUniversalSection (Y : Scheme.{u}) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    ((rootsOfUnitySheaf.{u, v} Y n).obj ⋙
      CategoryTheory.forget AddCommGrpCat).IsRepresentedBy
      (rootsOfUnityUniversalSection.{u, v} Y n hn) :=
  isRepresentedBy_rootsOfUnitySheaf_of_naturality.{u, v} Y n _ (rootsOfUnityEtaleHomEquiv Y n hn)
    (rootsOfUnityEtaleHomEquiv_naturality Y n hn)

/-- The universal `n`-th root of unity pulled back to the base change, as a section of `μ_n` on
the small étale site of `X`. -/
def rootsOfUnityBaseChangeUniversalSection {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj
      (op ((smallEtaleBaseChange π).obj (rootsOfUnityEtaleObj Y n hn)))) :=
  (rootsOfUnitySectionsEquiv.{u, v} X n
    (op ((smallEtaleBaseChange π).obj (rootsOfUnityEtaleObj Y n hn)))).symm
    (rootsOfUnityEtaleBaseChangeHomEquiv π n hn _ (𝟙 _))

/-- **`μ_n` on the small étale site of `X` is represented by the base change of the scheme of
`n`-th roots of unity over `Y`**, with universal element the pullback of the universal root of
unity.  This is where `n` being invertible on `Y` enters: it makes the representing object étale
over `Y`, hence its base change an object of the small étale site of `X`. -/
theorem isRepresentedBy_rootsOfUnityBaseChangeUniversalSection {X Y : Scheme.{u}} (π : X ⟶ Y)
    (n : ℕ) (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    ((rootsOfUnitySheaf.{u, v} X n).obj ⋙
      CategoryTheory.forget AddCommGrpCat).IsRepresentedBy
      (rootsOfUnityBaseChangeUniversalSection.{u, v} π n hn) :=
  isRepresentedBy_rootsOfUnitySheaf_of_naturality.{u, v} X n _
    (rootsOfUnityEtaleBaseChangeHomEquiv π n hn)
    (rootsOfUnityEtaleBaseChangeHomEquiv_naturality π n hn)

/-- **The comparison on `𝐆_m` commutes with the `n`-th power map.**  The `n`-th power map is
multiplication by `n` in the additive notation of the coefficient category, and both an additive
functor and a morphism of abelian sheaves commute with it. -/
theorem multiplicativeInverseImageComparison_comm_powMap {X Y : Scheme.{u}} (π : X ⟶ Y)
    (n : ℕ) :
    (etaleAbelianInverseImage.{u, v} π).map (powMap.{u, v} Y n) ≫
        multiplicativeInverseImageComparison.{u, v} π =
      multiplicativeInverseImageComparison.{u, v} π ≫ powMap.{u, v} X n := by
  let P := etaleAbelianInverseImage.{u, v} π
  let c := multiplicativeInverseImageComparison.{u, v} π
  change P.map (n • 𝟙 (multiplicativeSheaf.{u, v} Y)) ≫ c =
    c ≫ (n • 𝟙 (multiplicativeSheaf.{u, v} X))
  rw [P.map_nsmul]
  calc (n • P.map (𝟙 (multiplicativeSheaf.{u, v} Y))) ≫ c
      = (n • 𝟙 (P.obj (multiplicativeSheaf.{u, v} Y))) ≫ c :=
        congrArg (fun f => (n • f) ≫ c) (P.map_id (multiplicativeSheaf.{u, v} Y))
    _ = n • c := (Preadditive.nsmul_comp _ _ _).trans (congrArg (n • ·) (Category.id_comp c))
    _ = c ≫ (n • 𝟙 (multiplicativeSheaf.{u, v} X)) :=
        ((Preadditive.comp_nsmul _ _ _).trans (congrArg (n • ·) (Category.comp_id c))).symm

/-- **The comparison `π^{-1} μ_{n,Y} ⟶ μ_{n,X}`**: the comparison on `𝐆_m` read on kernels of
the `n`-th power map, using that inverse image preserves kernels. -/
def rootsOfUnityInverseImageComparison {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ) :
    (etaleAbelianInverseImage.{u, v} π).obj (rootsOfUnitySheaf.{u, v} Y n) ⟶
      rootsOfUnitySheaf.{u, v} X n :=
  kernelComparison (powMap.{u, v} Y n) (etaleAbelianInverseImage.{u, v} π) ≫
    kernel.map ((etaleAbelianInverseImage.{u, v} π).map (powMap.{u, v} Y n))
      (powMap.{u, v} X n) (multiplicativeInverseImageComparison.{u, v} π)
      (multiplicativeInverseImageComparison.{u, v} π)
      (multiplicativeInverseImageComparison_comm_powMap.{u, v} π n)

/-- **The comparison on `μ_n` is compatible with the inclusions into `𝐆_m`.**  Since the
inclusion of `μ_{n,X}` is a monomorphism, this characterises the comparison. -/
theorem rootsOfUnityInverseImageComparison_comp_rootsOfUnityι {X Y : Scheme.{u}} (π : X ⟶ Y)
    (n : ℕ) :
    rootsOfUnityInverseImageComparison.{u, v} π n ≫ rootsOfUnityι.{u, v} X n =
      (etaleAbelianInverseImage.{u, v} π).map (rootsOfUnityι.{u, v} Y n) ≫
        multiplicativeInverseImageComparison.{u, v} π := by
  have h1 : kernel.map ((etaleAbelianInverseImage.{u, v} π).map (powMap.{u, v} Y n))
      (powMap.{u, v} X n) (multiplicativeInverseImageComparison.{u, v} π)
      (multiplicativeInverseImageComparison.{u, v} π)
      (multiplicativeInverseImageComparison_comm_powMap.{u, v} π n) ≫
        kernel.ι (powMap.{u, v} X n) =
      kernel.ι ((etaleAbelianInverseImage.{u, v} π).map (powMap.{u, v} Y n)) ≫
        multiplicativeInverseImageComparison.{u, v} π :=
    kernel.lift_ι _ _ _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => kernelComparison (powMap.{u, v} Y n)
    (etaleAbelianInverseImage.{u, v} π) ≫ z) h1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun z => z ≫ multiplicativeInverseImageComparison.{u, v} π)
    (kernelComparison_comp_ι (powMap.{u, v} Y n) (etaleAbelianInverseImage.{u, v} π))

/-- If `n` is invertible on `Y` it is invertible on any `Y`-scheme, in particular on `X`. -/
theorem isUnit_natCast_of_hom {X Y : Scheme.{u}} (π : X ⟶ Y) {n : ℕ}
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) : IsUnit ((n : ℕ) : Γ(X, ⊤)) := by
  simpa using hn.map π.appTop.hom

/-- **The comparison `π^{-1} μ_{n,Y} ⟶ μ_{n,X}` is an isomorphism** when `n` is invertible on
`Y`.  Both sides have an underlying sheaf of sets represented by an object of the respective
small étale site — the scheme of `n`-th roots of unity over `Y` and its base change — and the
transpose of the comparison carries the universal root of unity to its pullback, which is the
universal root of unity on the base change. -/
@[sga "4 XIX 3.3" "For S'→S, special case"]
theorem isIso_rootsOfUnityInverseImageComparison {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    IsIso (rootsOfUnityInverseImageComparison.{u, v} π n) := by
  have hz := congrArg
    ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv
      (rootsOfUnitySheaf.{u, v} Y n) (multiplicativeSheaf.{u, v} X))
    (rootsOfUnityInverseImageComparison_comp_rootsOfUnityι.{u, v} π n)
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    multiplicativeInverseImageComparison_transpose] at hz
  have hz2 := congrArg (fun φ : rootsOfUnitySheaf.{u, v} Y n ⟶
      (etaleAbelianDirectImage.{u, v} π).obj (multiplicativeSheaf.{u, v} X) =>
    φ.hom.app (op (rootsOfUnityEtaleObj Y n hn)) (rootsOfUnityUniversalSection.{u, v} Y n hn)) hz
  have ha : rootsOfUnitySection.{u, v} Y n (op (rootsOfUnityEtaleObj Y n hn))
      (rootsOfUnityUniversalSection.{u, v} Y n hn) =
      rootsOfUnityEtaleHomEquiv Y n hn (rootsOfUnityEtaleObj Y n hn) (𝟙 _) :=
    (rootsOfUnitySectionsEquiv.{u, v} Y n (op (rootsOfUnityEtaleObj Y n hn))).apply_symm_apply _
  have hb : ((etaleAbelianInverseImageDirectImageAdj.{u, v} π).homEquiv
      (rootsOfUnitySheaf.{u, v} Y n) (rootsOfUnitySheaf.{u, v} X n)
      (rootsOfUnityInverseImageComparison.{u, v} π n)).hom.app
        (op (rootsOfUnityEtaleObj Y n hn)) (rootsOfUnityUniversalSection.{u, v} Y n hn) =
      rootsOfUnityBaseChangeUniversalSection.{u, v} π n hn := by
    refine (rootsOfUnitySectionsEquiv.{u, v} X n
      (op ((smallEtaleBaseChange π).obj (rootsOfUnityEtaleObj Y n hn)))).injective ?_
    have hu : rootsOfUnitySectionsEquiv.{u, v} X n
        (op ((smallEtaleBaseChange π).obj (rootsOfUnityEtaleObj Y n hn)))
        (rootsOfUnityBaseChangeUniversalSection.{u, v} π n hn) =
        rootsOfUnityEtaleBaseChangeHomEquiv π n hn _ (𝟙 _) :=
      (rootsOfUnitySectionsEquiv.{u, v} X n _).apply_symm_apply _
    rw [hu]
    refine Subtype.ext (ofUnit_injective.{u, v} ?_)
    refine (rootsOfUnityι_app_eq_ofUnit.{u, v} X n _ _).symm.trans (hz2.trans ?_)
    refine (congrArg (fun z => (multiplicativeDirectImageComparison.{u, v} π).hom.app
      (op (rootsOfUnityEtaleObj Y n hn)) z)
      ((rootsOfUnityι_app_eq_ofUnit.{u, v} Y n (op (rootsOfUnityEtaleObj Y n hn))
        (rootsOfUnityUniversalSection.{u, v} Y n hn)).trans
        (congrArg ofUnit (congrArg Subtype.val ha)))).trans ?_
    exact (multiplicativeDirectImageComparison_app_ofUnit.{u, v} π _ _).trans
      (congrArg ofUnit (rootsOfUnityEtaleBaseChangeHomEquiv_id π n hn).symm)
  refine isIso_of_isRepresentedBy_transpose Y.smallEtaleTopology X.smallEtaleTopology
    (smallEtaleBaseChange π) (etaleAbelianInverseImageDirectImageAdj.{u, v} π)
    (rootsOfUnitySheaf.{u, v} Y n) (rootsOfUnitySheaf.{u, v} X n)
    (rootsOfUnityInverseImageComparison.{u, v} π n) (rootsOfUnityEtaleObj Y n hn)
    (rootsOfUnityUniversalSection.{u, v} Y n hn)
    (isRepresentedBy_rootsOfUnityUniversalSection.{u, v} Y n hn) ?_
  rw [hb]
  exact isRepresentedBy_rootsOfUnityBaseChangeUniversalSection.{u, v} π n hn

/-- **The isomorphism `π^{-1} μ_{n,Y} ≅ μ_{n,X}`** for `n` invertible on `Y`, given by the
comparison morphism and hence compatible with the two inclusions into `𝐆_m`. -/
def rootsOfUnityInverseImageIso {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    (etaleAbelianInverseImage.{u, v} π).obj (rootsOfUnitySheaf.{u, v} Y n) ≅
      rootsOfUnitySheaf.{u, v} X n :=
  haveI := isIso_rootsOfUnityInverseImageComparison.{u, v} π n hn
  asIso (rootsOfUnityInverseImageComparison.{u, v} π n)

/-- The forward morphism of `rootsOfUnityInverseImageIso` is the comparison morphism
`rootsOfUnityInverseImageComparison π n`. -/
@[simp]
theorem rootsOfUnityInverseImageIso_hom {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤))) :
    (rootsOfUnityInverseImageIso.{u, v} π n hn).hom =
      rootsOfUnityInverseImageComparison.{u, v} π n :=
  rfl

end RootsComparison

section KummerSequenceComparison

/-- **The morphism from the inverse image of the Kummer sequence of `Y` to the Kummer sequence of
`X`**: the comparison on `μ_n` on the subsheaves and the comparison on `𝐆_m` on the other two
terms.  Its first component is an isomorphism when `n` is invertible on `Y`. -/
def kummerSequenceInverseImageMap {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ) :
    (kummerSequence.{u, v} Y n).map (etaleAbelianInverseImage.{u, v} π) ⟶
      kummerSequence.{u, v} X n where
  τ₁ := rootsOfUnityInverseImageComparison.{u, v} π n
  τ₂ := multiplicativeInverseImageComparison.{u, v} π
  τ₃ := multiplicativeInverseImageComparison.{u, v} π
  comm₁₂ := rootsOfUnityInverseImageComparison_comp_rootsOfUnityι.{u, v} π n
  comm₂₃ := (multiplicativeInverseImageComparison_comm_powMap.{u, v} π n).symm

/-- The first component of `kummerSequenceInverseImageMap` is the comparison morphism on `μ_n`. -/
@[simp]
theorem kummerSequenceInverseImageMap_τ₁ {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ) :
    (kummerSequenceInverseImageMap.{u, v} π n).τ₁ =
      rootsOfUnityInverseImageComparison.{u, v} π n :=
  rfl

/-- The third component of `kummerSequenceInverseImageMap` is the comparison morphism on `𝐆_m`. -/
@[simp]
theorem kummerSequenceInverseImageMap_τ₃ {X Y : Scheme.{u}} (π : X ⟶ Y) (n : ℕ) :
    (kummerSequenceInverseImageMap.{u, v} π n).τ₃ =
      multiplicativeInverseImageComparison.{u, v} π :=
  rfl

/-- **The Kummer coboundary square.**  For a class `x ∈ H^q(Y, 𝐆_m)` the restriction along `π` of
its Kummer coboundary in `H^r(Y, μ_n)`, transported to `H^r(X, μ_n)` along the comparison on
`μ_n`, is the Kummer coboundary of the restriction of `x` transported along the comparison on
`𝐆_m`.

Both sides are read in the cohomology of `X`: restriction lands in the cohomology of the inverse
image of the coefficient sheaf, and the comparison morphisms move it to the cohomology of the
Kummer sheaves of `X`. -/
theorem etaleCohomologyRestrictionMap_kummerExtClass {X Y : Scheme.{u}} (π : X ⟶ Y) {n : ℕ}
    (hn0 : n ≠ 0) (hn : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (q r : ℕ) (hqr : q + 1 = r) (x : Sheaf.H.{w} (multiplicativeSheaf.{u, v} Y) q) :
    Sheaf.H.map (rootsOfUnityInverseImageComparison.{u, v} π n) r
        (etaleCohomologyRestrictionMap.{u, v, w} π (rootsOfUnitySheaf.{u, v} Y n) r
          (x.comp (kummerSequence_shortExact.{u, v} Y hn0 hn).extClass hqr)) =
      (Sheaf.H.map (multiplicativeInverseImageComparison.{u, v} π) q
          (etaleCohomologyRestrictionMap.{u, v, w} π (multiplicativeSheaf.{u, v} Y) q x)).comp
        (kummerSequence_shortExact.{u, v} X hn0 (isUnit_natCast_of_hom π hn)).extClass hqr := by
  have h1 : etaleCohomologyRestrictionMap.{u, v, w} π (rootsOfUnitySheaf.{u, v} Y n) r
      (x.comp (kummerSequence_shortExact.{u, v} Y hn0 hn).extClass hqr) =
      (etaleCohomologyRestrictionMap.{u, v, w} π (multiplicativeSheaf.{u, v} Y) q x).comp
        ((kummerSequence_shortExact.{u, v} Y hn0 hn).map_of_exact
          (etaleAbelianInverseImage.{u, v} π)).extClass hqr :=
    etaleCohomologyRestrictionMap_comp_extClass.{u, v, w} π
      (kummerSequence_shortExact.{u, v} Y hn0 hn) q r hqr x
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply, h1,
    ← kummerSequenceInverseImageMap_τ₁.{u, v} π n, ← kummerSequenceInverseImageMap_τ₃.{u, v} π n]
  refine (Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ hqr).trans ?_
  refine (congrArg (fun z => (etaleCohomologyRestrictionMap.{u, v, w} π
    (multiplicativeSheaf.{u, v} Y) q x).comp z hqr)
    (ShortComplex.ShortExact.extClass_naturality
      ((kummerSequence_shortExact.{u, v} Y hn0 hn).map_of_exact
        (etaleAbelianInverseImage.{u, v} π))
      (kummerSequence_shortExact.{u, v} X hn0 (isUnit_natCast_of_hom π hn))
      (kummerSequenceInverseImageMap.{u, v} π n))).trans ?_
  exact (Abelian.Ext.comp_assoc_of_second_deg_zero _ _ _ hqr).symm

end KummerSequenceComparison



end Stacks.Kummer

end
