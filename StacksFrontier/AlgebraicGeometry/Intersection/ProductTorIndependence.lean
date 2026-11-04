module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TorIndependenceBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk

/-!
# Tor independence of the two factors of a product over a field

Let `X` and `Y` be schemes over the spectrum of a field `k`, let `I` be a sheaf of ideals on `X`
and `J` one on `Y`. The closed subschemes `pr_X⁻¹(I)` and `pr_Y⁻¹(J)` of `X ×_k Y`, that is
`V(I) ×_k Y` and `X ×_k V(J)`, are Tor independent over `X ×_k Y`: at every point `z` lying on
both, `Tor_i^{𝒪_{X ×_k Y, z}}(𝒪_{X ×_k Y, z} ⧸ I_z, 𝒪_{X ×_k Y, z} ⧸ J_z) = 0` for `i > 0`.

This is the vanishing behind the identity `α × β = (α × [Y]) · ([X] × β)` of Stacks 0B0R: it
says that the intersection product of `V × Y` and `X × W` is computed by `Tor_0` alone, which is
the structure sheaf of `V × W`.

## Main results

* `AlgebraicGeometry.TorIndependent.iso_left`: Tor independence is invariant under replacing the
  source of the first morphism by an isomorphic scheme.
* `AlgebraicGeometry.torIndependent_postcomp_iso_iff`: Tor independence is invariant under an
  isomorphism of the base.
* `AlgebraicGeometry.torIndependent_pullback_fst_of_flat`: for `p : P ⟶ X` flat and
  `j : W ⟶ P` with `j ≫ p` flat, the base change of any `i : V ⟶ X` along `p` is Tor
  independent from `j` over `P`. This is Stacks 0CTA in the special case of an identity.
* `AlgebraicGeometry.torIndependent_comap_fst_comap_snd`: the closed subschemes `pr_X⁻¹(I)` and
  `pr_Y⁻¹(J)` of a product over a field are Tor independent.
* `AlgebraicGeometry.tor_subsingleton_stalk_comap_fst_comap_snd`: the same statement read at
  the local rings of the product, as the vanishing of the higher Tor modules of the two
  quotients `𝒪_{X ×_k Y, z} ⧸ I_z` and `𝒪_{X ×_k Y, z} ⧸ J_z`.

## References

* [Stacks Project, Tag 0CTA](https://stacks.math.columbia.edu/tag/0CTA)
* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
* [Stacks Project, Tag 0B0R](https://stacks.math.columbia.edu/tag/0B0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Tor independence is invariant under replacing the source of the first morphism by an
isomorphic scheme: the local rings correspond under the isomorphism, compatibly with the maps
from the local rings of the base. -/
theorem TorIndependent.iso_left {S X X' Y : Scheme.{u}} (e : X' ≅ X) {f : X ⟶ S} {g : Y ⟶ S}
    (H : TorIndependent f g) : TorIndependent (e.hom ≫ f) g := by
  intro x y h
  let R := S.presheaf.stalk (f.base (e.hom.base x))
  let : Algebra R (X.presheaf.stalk (e.hom.base x)) := (f.stalkMap (e.hom.base x)).hom.toAlgebra
  let : Algebra R (X'.presheaf.stalk x) := ((e.hom ≫ f).stalkMap x).hom.toAlgebra
  let : Algebra R (Y.presheaf.stalk y) :=
    (eqToHom (congrArg (fun z => S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
  let a : X.presheaf.stalk (e.hom.base x) →ₗ[R] X'.presheaf.stalk x :=
    { __ := (e.hom.stalkMap x).hom.toAddMonoidHom
      map_smul' := by
        intro r m
        change (e.hom.stalkMap x).hom ((f.stalkMap (e.hom.base x)).hom r * m) =
          ((e.hom ≫ f).stalkMap x).hom r * (e.hom.stalkMap x).hom m
        rw [map_mul, Scheme.Hom.stalkMap_comp]
        rfl }
  let aIso := (LinearEquiv.ofBijective a
    (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap x))).toModuleIso
  intro n hn
  exact IsZero.of_iso (H (e.hom.base x) y h n hn) (((Tor (ModuleCat R) n).mapIso aIso).app
    (ModuleCat.of R (Y.presheaf.stalk y))).symm

/-- Transporting a map of local rings along an equality of points of the base and then along the
map on stalks of a morphism of bases. -/
private theorem stalkMap_transport_comp {S S' X : Scheme.{u}} (e : S ⟶ S') (f : X ⟶ S) (x : X)
    (s : S) (h : s = f.base x) :
    eqToHom (congrArg (fun t => S'.presheaf.stalk t) (congrArg e.base h)) ≫
      (f ≫ e).stalkMap x =
    e.stalkMap s ≫ eqToHom (congrArg (fun t => S.presheaf.stalk t) h) ≫ f.stalkMap x := by
  subst s
  simp [Scheme.Hom.stalkMap_comp]

/-- Tor independence is invariant under an isomorphism of the base: the local rings of the two
bases correspond under the isomorphism, and restriction of scalars along a ring isomorphism
reflects and preserves the vanishing of Tor. -/
theorem torIndependent_postcomp_iso_iff {S S' X Y : Scheme.{u}} (e : S ≅ S') (f : X ⟶ S)
    (g : Y ⟶ S) :
    TorIndependent (f ≫ e.hom) (g ≫ e.hom) ↔ TorIndependent f g := by
  have heq (x : X) (y : Y) (h : f.base x = g.base y) :
      let R := S'.presheaf.stalk (e.hom.base (f.base x))
      let R' := S.presheaf.stalk (f.base x)
      let : Algebra R' (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
      let : Algebra R' (Y.presheaf.stalk y) :=
        (eqToHom (congrArg (fun z => S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
      let : Algebra R (X.presheaf.stalk x) := ((f ≫ e.hom).stalkMap x).hom.toAlgebra
      let : Algebra R (Y.presheaf.stalk y) :=
        (eqToHom (congrArg (fun z => S'.presheaf.stalk z) (congrArg e.hom.base h)) ≫
          (g ≫ e.hom).stalkMap y).hom.toAlgebra
      Algebra.TorIndependent R (X.presheaf.stalk x) (Y.presheaf.stalk y) ↔
        Algebra.TorIndependent R' (X.presheaf.stalk x) (Y.presheaf.stalk y) := by
    dsimp only
    let R := S'.presheaf.stalk (e.hom.base (f.base x))
    let R' := S.presheaf.stalk (f.base x)
    let eR : R ≃+* R' := (asIso (e.hom.stalkMap (f.base x))).commRingCatIsoToRingEquiv
    let : Algebra R' (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    let : Algebra R' (Y.presheaf.stalk y) :=
      (eqToHom (congrArg (fun z => S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
    have hA : (ModuleCat.restrictScalars eR.toRingHom).obj
        (ModuleCat.of R' (X.presheaf.stalk x)) =
        @ModuleCat.of R _ _ _ (((f ≫ e.hom).stalkMap x).hom.toAlgebra.toModule) := by
      dsimp only [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj', ModuleCat.of]
      congr 1
      apply Module.ext
      funext a b
      change (f.stalkMap x).hom ((e.hom.stalkMap (f.base x)).hom a) * b =
        ((f ≫ e.hom).stalkMap x).hom a * b
      rw [Scheme.Hom.stalkMap_comp]
      rfl
    have hB : (ModuleCat.restrictScalars eR.toRingHom).obj
        (ModuleCat.of R' (Y.presheaf.stalk y)) =
        @ModuleCat.of R _ _ _ ((eqToHom (congrArg (fun z => S'.presheaf.stalk z)
          (congrArg e.hom.base h)) ≫ (g ≫ e.hom).stalkMap y).hom.toAlgebra.toModule) := by
      dsimp only [ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj', ModuleCat.of]
      congr 1
      apply Module.ext
      funext a b
      change (e.hom.stalkMap (f.base x) ≫ eqToHom (congrArg (fun z => S.presheaf.stalk z) h) ≫
        g.stalkMap y).hom a * b = _
      rw [← stalkMap_transport_comp e.hom g y (f.base x) h]
      rfl
    change (∀ n : ℕ, 0 < n → _) ↔ (∀ n : ℕ, 0 < n → _)
    apply forall_congr' fun n => forall_congr' fun hn => ?_
    have hi := RingTheory.TorIndependence.isZero_tor_restrict_iff eR
      (ModuleCat.of R' (X.presheaf.stalk x)) (ModuleCat.of R' (Y.presheaf.stalk y)) n
    rwa [hA, hB] at hi
  refine ⟨fun H x y h => (heq x y h).mp (H x y (congrArg e.hom.base h)), fun H x y h => ?_⟩
  have h' : f.base x = g.base y := e.hom.homeomorph.injective h
  exact (heq x y h').mpr (H x y h')

/-- **Stacks 0CTA for an identity morphism.** For `p : P ⟶ X` flat and `j : W ⟶ P` with
`j ≫ p` flat, the base change `P ×_X V ⟶ P` of any morphism `i : V ⟶ X` along `p` is Tor
independent from `j` over `P`. -/
theorem torIndependent_pullback_fst_of_flat {X P V W : Scheme.{u}} (i : V ⟶ X) (p : P ⟶ X)
    (j : W ⟶ P) [Flat p] [Flat (j ≫ p)] :
    TorIndependent (pullback.fst p i) j := by
  have H := torIndependent_pullback_product_of_flat i (𝟙 X) p (j ≫ p) j (by simp)
  let a := pullback.snd (𝟙 X) i
  let b := pullback.snd p i
  let e : pullback (𝟙 X) p ≅ P := asIso (pullback.snd (𝟙 X) p)
  have H' := (torIndependent_postcomp_iso_iff e _ _).mpr H
  simp only [e, asIso_hom, pullback.lift_snd] at H'
  let e' : pullback p i ≅ pullback a b := (asIso (pullback.snd a b)).symm
  simpa only [e', a, b, Iso.symm_hom, asIso_inv, Category.assoc,
    IsIso.inv_hom_id_assoc] using TorIndependent.iso_left e' H'

/-- **The closed subschemes `V(I) ×_k Y` and `X ×_k V(J)` of a product over a field are Tor
independent.** The second is flat over `X`, being the base change of `V(J) ⟶ Spec k`, and the
first is the base change along the flat projection `pr_X` of the closed immersion `V(I) ⟶ X`;
Stacks 0CTA then gives the Tor independence. -/
theorem torIndependent_comap_fst_comap_snd (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (J : Y.IdealSheafData) :
    TorIndependent (I.comap (pullback.fst f g)).subschemeι
      (J.comap (pullback.snd f g)).subschemeι := by
  let p := pullback.fst f g
  let B := J.comap (pullback.snd f g)
  let e := (J.comapIso (pullback.snd f g)).trans (pullbackLeftPullbackSndIso f g J.subschemeι)
  have he : e.hom ≫ pullback.fst f (J.subschemeι ≫ g) = B.subschemeι ≫ p := by
    simp [e, B, p, Category.assoc]
  have : Flat (B.subschemeι ≫ p) := by
    rw [← he]
    infer_instance
  simpa only [Scheme.IdealSheafData.comapIso_hom_fst] using
    TorIndependent.iso_left (I.comapIso p)
      (torIndependent_pullback_fst_of_flat I.subschemeι p B.subschemeι)

/-- **Vanishing of the higher Tor modules of two Tor-independent closed subschemes, at a local
ring.** If the closed subschemes cut out by `I` and `J` are Tor independent, then at every point
`z` of both, `Tor_i^{𝒪_{X, z}}(𝒪_{X, z} ⧸ I_z, 𝒪_{X, z} ⧸ J_z) = 0` for `i > 0`: the two
quotients are the local rings of the two closed subschemes. -/
theorem tor_subsingleton_stalk_of_torIndependent {X : Scheme.{u}} (I J : X.IdealSheafData)
    (H : TorIndependent I.subschemeι J.subschemeι) (z : X) (hzI : z ∈ I.support)
    (hzJ : z ∈ J.support) (i : ℕ) (hi : 0 < i) :
    Subsingleton (((Tor (ModuleCat.{u} (X.presheaf.stalk z)) i).obj
        (ModuleCat.of (X.presheaf.stalk z) (X.presheaf.stalk z ⧸ IdealSheafData.stalk I z))).obj
      (ModuleCat.of (X.presheaf.stalk z) (X.presheaf.stalk z ⧸ IdealSheafData.stalk J z))) := by
  let v := IdealSheafData.subschemePoint I z hzI
  let w := IdealSheafData.subschemePoint J z hzJ
  let R := X.presheaf.stalk z
  let : Algebra R (I.subscheme.presheaf.stalk v) := (I.subschemeι.stalkMap v).hom.toAlgebra
  let : Algebra R (J.subscheme.presheaf.stalk w) := (J.subschemeι.stalkMap w).hom.toAlgebra
  have hH' : IsZero (((Tor (ModuleCat.{u} R) i).obj
      (ModuleCat.of R (I.subscheme.presheaf.stalk v))).obj
        (ModuleCat.of R (J.subscheme.presheaf.stalk w))) :=
    H v w rfl i hi
  let eI : ModuleCat.of R (R ⧸ IdealSheafData.stalk I z) ≅
      ModuleCat.of R (I.subscheme.presheaf.stalk v) :=
    (IdealSheafData.subschemeStalkQuotLinearEquiv I v).toModuleIso
  let eJ : ModuleCat.of R (R ⧸ IdealSheafData.stalk J z) ≅
      ModuleCat.of R (J.subscheme.presheaf.stalk w) :=
    (IdealSheafData.subschemeStalkQuotLinearEquiv J w).toModuleIso
  exact ModuleCat.isZero_iff_subsingleton.mp <| IsZero.of_iso hH'
    (((Tor (ModuleCat R) i).mapIso eI).app _ ≪≫
      ((Tor (ModuleCat R) i).obj (ModuleCat.of R (I.subscheme.presheaf.stalk v))).mapIso eJ)

/-- **The higher Tor modules of `V(I) ×_k Y` and `X ×_k V(J)` vanish at every local ring of the
product.** At a point `z` of `X ×_k Y` lying on both closed subschemes,
`Tor_i^{𝒪_{X ×_k Y, z}}(𝒪_{X ×_k Y, z} ⧸ (pr_X⁻¹ I)_z, 𝒪_{X ×_k Y, z} ⧸ (pr_Y⁻¹ J)_z) = 0`
for every `i > 0`. -/
theorem tor_subsingleton_stalk_comap_fst_comap_snd (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (J : Y.IdealSheafData) (z : (pullback f g : Scheme.{u}))
    (hzI : z ∈ (I.comap (pullback.fst f g)).support)
    (hzJ : z ∈ (J.comap (pullback.snd f g)).support) (i : ℕ) (hi : 0 < i) :
    Subsingleton (((Tor (ModuleCat.{u} ((pullback f g : Scheme.{u}).presheaf.stalk z)) i).obj
        (ModuleCat.of ((pullback f g : Scheme.{u}).presheaf.stalk z)
          ((pullback f g : Scheme.{u}).presheaf.stalk z ⧸
            IdealSheafData.stalk (I.comap (pullback.fst f g)) z))).obj
      (ModuleCat.of ((pullback f g : Scheme.{u}).presheaf.stalk z)
        ((pullback f g : Scheme.{u}).presheaf.stalk z ⧸
          IdealSheafData.stalk (J.comap (pullback.snd f g)) z))) :=
  tor_subsingleton_stalk_of_torIndependent _ _
    (torIndependent_comap_fst_comap_snd k f g I J) z hzI hzJ i hi

end AlgebraicGeometry

end
