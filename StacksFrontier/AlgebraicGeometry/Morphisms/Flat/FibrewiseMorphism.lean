module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewisePoint
import StacksFrontier.AlgebraicGeometry.Flatness.ThickeningBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of a morphism detected on the fibres of the base

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes with `X` locally of finite
presentation and flat over `S`, with `Y` locally of finite type over `S`, and with the induced
morphism `f_s : X_s ⟶ Y_s` flat for every point `s` of `S`. Then `f` is flat, and if `f` is
moreover surjective then `g` is flat.

Both conclusions are read off the same pointwise statement: at a point `x` of `X` with
`y = f x` and `s = g y`, the local ring `𝒪_{X,x}` is flat over `𝒪_{S,s}` and its fibre
`𝒪_{X,x}/𝔪_s 𝒪_{X,x}` is flat over `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}`, so the fibrewise criterion
`Stacks.Flatness.flat_and_flat_fibre_stalk_iff` gives that `𝒪_{Y,y}` is flat over `𝒪_{S,s}`
and `𝒪_{X,x}` is flat over `𝒪_{Y,y}`. A surjective `f` reaches every point of `Y`, which turns
the first of these into flatness of `g`.

## Main results

* `Stacks.Flatness.flat_of_flat_fiberHom`: `f` is flat.
* `Stacks.Flatness.flat_of_flat_fiberHom_of_surjective`: `g` is flat when `f` is surjective.

## Implementation notes

The criterion `Stacks.Flatness.flat_and_flat_fibre_stalk_iff` phrases the fibre condition with
the quotients `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}` and `𝒪_{X,x}/𝔪_s 𝒪_{X,x}` of stalks, whereas the
hypothesis here is flatness of the morphism `f_s` of fibre schemes. Identifying the two is the
work of `Stacks.Flatness.flat_quotient_of_flat_fiberHom`: the quotients are the local rings of
the fibres by `AlgebraicGeometry.quotientStalkEquivFiberStalk`, and the square comparing the
stalk map of `f_s` with the stalk map of `f` is the naturality of stalk maps for the commuting
square `X_s ⟶ X ⟶ Y = X_s ⟶ Y_s ⟶ Y`.

## References

* [Stacks Project, Tag 039E](https://stacks.math.columbia.edu/tag/039E)
* [Stacks Project, Tag 039C](https://stacks.math.columbia.edu/tag/039C)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Flatness

/-- **Naturality of stalk maps for a commuting square of schemes.** For a commuting square
`i ≫ f = p ≫ q` and a point `v` of its upper left corner, the two composites of stalk maps
out of the stalk at the image of `v` in the lower right corner agree, after the canonical
identifications of stalks at equal points. -/
private theorem stalkMap_square {V W X Y : Scheme.{u}} (i : V ⟶ X) (f : X ⟶ Y)
    (p : V ⟶ W) (q : W ⟶ Y) (hsq : i ≫ f = p ≫ q) (v : V)
    {x : X} (hx : x = i v) {w : W} (hw : w = p v) (hy : f x = q w) :
    f.stalkMap x ≫ (X.presheaf.stalkCongr (.of_eq hx)).hom ≫ i.stalkMap v
      = (Y.presheaf.stalkCongr (.of_eq hy)).hom ≫ q.stalkMap w ≫
          (W.presheaf.stalkCongr (.of_eq hw)).hom ≫ p.stalkMap v := by
  subst hx
  subst hw
  have h := Scheme.Hom.stalkMap_congr_hom (i ≫ f) (p ≫ q) hsq v
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp,
    TopCat.Presheaf.stalkCongr_hom] at h
  simpa using h

/-- The canonical point of the fibre of `f ≫ g` through `x` is carried by the morphism of
fibres to the canonical point of the fibre of `g` through `f x`. -/
private theorem fiberHom_asFiber {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    fiberHom f g ((f ≫ g) x) ((f ≫ g).asFiber x) = g.asFiber (f x) := by
  apply (g.fiberι ((f ≫ g) x)).isEmbedding.injective
  have h : fiberHom f g ((f ≫ g) x) ≫ g.fiberι ((f ≫ g) x)
      = (f ≫ g).fiberι ((f ≫ g) x) ≫ f := Limits.pullback.lift_fst ..
  have h2 := congrArg (fun k : _ ⟶ Y => k ((f ≫ g).asFiber x)) h
  simp only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber] at h2
  exact h2.trans (Scheme.Hom.fiberι_asFiber g (f x)).symm

/-- The local ring of the fibre `Y_s` at the image of the canonical point of `X_s`, presented
as the quotient `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}` of stalks. -/
private noncomputable def fiberStalkRingEquiv {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (x : X) :
    (Y.presheaf.stalk (f x) ⧸ Ideal.map (g.stalkMap (f x)).hom
        (maximalIdeal (S.presheaf.stalk (g (f x)))))
      ≃+* (g.fiber ((f ≫ g) x)).presheaf.stalk
        (fiberHom f g ((f ≫ g) x) ((f ≫ g).asFiber x)) :=
  (AlgebraicGeometry.quotientStalkEquivFiberStalk g (f x)).trans
    ((g.fiber ((f ≫ g) x)).presheaf.stalkCongr
      (.of_eq (fiberHom_asFiber f g x).symm)).commRingCatIsoToRingEquiv

/-- **The square comparing the stalk map of the morphism of fibres with the stalk map of `f`.**
The stalk map of `f` descends to the quotients by the extended maximal ideal of `𝒪_{S,s}`, and
under the identification of those quotients with the local rings of the fibres the descended
map is the stalk map of `f_s`. -/
private theorem quotientStalk_fiberHom_square {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (x : X) (a : Y.presheaf.stalk (f x)) :
    AlgebraicGeometry.quotientStalkEquivFiberStalk (f ≫ g) x
        (Ideal.Quotient.mk (Ideal.map ((f ≫ g).stalkMap x).hom
          (maximalIdeal (S.presheaf.stalk ((f ≫ g) x)))) ((f.stalkMap x).hom a))
      = ((fiberHom f g ((f ≫ g) x)).stalkMap ((f ≫ g).asFiber x)).hom
          (fiberStalkRingEquiv f g x
            (Ideal.Quotient.mk (Ideal.map (g.stalkMap (f x)).hom
              (maximalIdeal (S.presheaf.stalk (g (f x))))) a)) :=
  (AlgebraicGeometry.quotientStalkEquivFiberStalk_mk (f ≫ g) x ((f.stalkMap x).hom a)).trans
    ((congrArg (fun k => CommRingCat.Hom.hom k a)
        (stalkMap_square ((f ≫ g).fiberι ((f ≫ g) x)) f (fiberHom f g ((f ≫ g) x))
          (g.fiberι ((f ≫ g) x)) (Limits.pullback.lift_fst ..).symm ((f ≫ g).asFiber x)
          ((f ≫ g).fiberι_asFiber x).symm (fiberHom_asFiber f g x).symm
          (g.fiberι_asFiber (f x)).symm)).trans
      (congrArg
        (fun t => ((fiberHom f g ((f ≫ g) x)).stalkMap ((f ≫ g).asFiber x)).hom
          (((g.fiber ((f ≫ g) x)).presheaf.stalkCongr
            (.of_eq (fiberHom_asFiber f g x).symm)).hom.hom t))
        (AlgebraicGeometry.quotientStalkEquivFiberStalk_mk g (f x) a).symm))

/-- The submodule that an ideal of `R` generates in a tower `R → A → C` after extension to `A`
is the ideal it generates in `C` directly. -/
private theorem smul_top_eq_restrictScalars_map {R A C : Type*} [CommRing R] [CommRing A]
    [CommRing C] [Algebra R A] [Algebra A C] [Algebra R C] [IsScalarTower R A C] (I : Ideal R) :
    (I.map (algebraMap R A) • (⊤ : Submodule A C))
      = Submodule.restrictScalars A (I.map (algebraMap R C)) := by
  rw [Ideal.smul_top_eq_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **Flatness of the fibre of a tower of rings, read through two ring equivalences.** For a
tower `R → A → C` and an ideal `I` of `R`, if the quotients `A/IA` and `C/IC` are identified
with rings `A'` and `C'` compatibly with the maps out of `A`, then flatness of `C'` over `A'`
gives flatness of `C/IC` over `A/IA`. -/
private theorem flat_quotient_of_flat_ringEquiv {R A C A' C' : Type*} [CommRing R] [CommRing A]
    [CommRing C] [CommRing A'] [CommRing C'] [Algebra R A] [Algebra A C] [Algebra R C]
    [IsScalarTower R A C] [Algebra A' C'] [Module.Flat A' C'] (I : Ideal R)
    (eA : (A ⧸ I.map (algebraMap R A)) ≃+* A')
    (eC : (C ⧸ I.map (algebraMap R C)) ≃+* C')
    (hcomm : ∀ a : A, eC (Ideal.Quotient.mk (I.map (algebraMap R C)) (algebraMap A C a))
      = algebraMap A' C' (eA (Ideal.Quotient.mk (I.map (algebraMap R A)) a))) :
    Module.Flat (A ⧸ I.map (algebraMap R A))
      (C ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A C))) := by
  refine flat_of_ringEquiv eA
    ((Submodule.quotEquivOfEq _ _ (smul_top_eq_restrictScalars_map I)).toAddEquiv.trans
      ((Submodule.Quotient.restrictScalarsEquiv A
        (I.map (algebraMap R C))).toAddEquiv.trans eC.toAddEquiv)) ?_
  intro q n
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  induction n using Submodule.Quotient.induction_on with
  | H c =>
    have hmk : (Ideal.Quotient.mk (I.map (algebraMap R A)) a) •
        (Submodule.Quotient.mk c : C ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A C)))
        = Submodule.Quotient.mk (a • c) := by
      rw [Module.IsTorsionBySet.mk_smul]
      rfl
    rw [hmk]
    change eC (Ideal.Quotient.mk (I.map (algebraMap R C)) (a • c))
      = _ • eC (Ideal.Quotient.mk (I.map (algebraMap R C)) c)
    rw [Algebra.smul_def a c, map_mul, map_mul, hcomm a, Algebra.smul_def]

/-- **The fibre condition of the fibrewise criterion, from flatness of the morphism of fibres.**
If the morphism `X_s ⟶ Y_s` of fibres over `s = g (f x)` is flat, then the fibre
`𝒪_{X,x}/𝔪_s 𝒪_{X,x}` is flat over `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}`. -/
private theorem flat_quotient_of_flat_fiberHom {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (x : X) [AlgebraicGeometry.Flat (fiberHom f g ((f ≫ g) x))] :
    let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Module.Flat
      (Y.presheaf.stalk (f x) ⧸ Ideal.map (g.stalkMap (f x)).hom
        (maximalIdeal (S.presheaf.stalk (g (f x)))))
      (X.presheaf.stalk x ⧸ (Ideal.map (g.stalkMap (f x)).hom
          (maximalIdeal (S.presheaf.stalk (g (f x)))) •
        (⊤ : Submodule (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)))) := by
  let _ : Algebra (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) :=
    (g.stalkMap (f x)).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Algebra (S.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
    ((f ≫ g).stalkMap x).hom.toAlgebra
  have : IsScalarTower (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (by
      change ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom
      rw [Scheme.Hom.stalkMap_comp]
      rfl)
  let _ : Algebra ((g.fiber ((f ≫ g) x)).presheaf.stalk
      (fiberHom f g ((f ≫ g) x) ((f ≫ g).asFiber x)))
      (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x)) :=
    ((fiberHom f g ((f ≫ g) x)).stalkMap ((f ≫ g).asFiber x)).hom.toAlgebra
  have : Module.Flat ((g.fiber ((f ≫ g) x)).presheaf.stalk
      (fiberHom f g ((f ≫ g) x) ((f ≫ g).asFiber x)))
      (((f ≫ g).fiber ((f ≫ g) x)).presheaf.stalk ((f ≫ g).asFiber x)) :=
    AlgebraicGeometry.Flat.stalkMap (fiberHom f g ((f ≫ g) x)) ((f ≫ g).asFiber x)
  exact flat_quotient_of_flat_ringEquiv (maximalIdeal (S.presheaf.stalk (g (f x))))
    (fiberStalkRingEquiv f g x)
    (AlgebraicGeometry.quotientStalkEquivFiberStalk (f ≫ g) x)
    (quotientStalk_fiberHom_square f g x)

/-- **The pointwise content of Stacks Tag 039E.** Under the hypotheses of the fibrewise
criterion, at every point `x` of `X` the local ring `𝒪_{Y,f x}` is flat over `𝒪_{S,g (f x)}`
and `𝒪_{X,x}` is flat over `𝒪_{Y,f x}`. -/
private theorem flat_stalkMap_of_flat_fiberHom {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g]
    [AlgebraicGeometry.Flat (f ≫ g)]
    (hfib : ∀ s : S, AlgebraicGeometry.Flat (fiberHom f g s)) (x : X) :
    (g.stalkMap (f x)).hom.Flat ∧ (f.stalkMap x).hom.Flat := by
  let _ : Algebra (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) :=
    (g.stalkMap (f x)).hom.toAlgebra
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Algebra (S.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
    ((f ≫ g).stalkMap x).hom.toAlgebra
  have : AlgebraicGeometry.Flat (fiberHom f g ((f ≫ g) x)) := hfib _
  exact (flat_and_flat_fibre_stalk_iff f g x (X.presheaf.stalk x) rfl
    (fun _ _ => rfl) (fun _ _ => rfl)).mp
    ⟨AlgebraicGeometry.Flat.stalkMap (f ≫ g) x, flat_quotient_of_flat_fiberHom f g x⟩

/-- **Stacks Project, Tag 039E.** Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes with
`X` locally of finite presentation and flat over `S`, with `Y` locally of finite type over `S`,
and with the morphism `X_s ⟶ Y_s` of fibres flat for every point `s` of `S`. Then `f` is
flat. -/
@[stacks 039E "flatness of the morphism", ega "IV 20.5.7" "partial", sga "1 I 5.9" "partial"]
public theorem flat_of_flat_fiberHom {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g]
    [AlgebraicGeometry.Flat (f ≫ g)]
    (hfib : ∀ s : S, AlgebraicGeometry.Flat (fiberHom f g s)) :
    AlgebraicGeometry.Flat f :=
  AlgebraicGeometry.Flat.of_stalkMap f fun x =>
    (flat_stalkMap_of_flat_fiberHom f g hfib x).2

/-- **Stacks Project, Tag 039E.** In the situation of
`Stacks.Flatness.flat_of_flat_fiberHom`, if `f` is moreover surjective then `Y` is flat
over `S`. -/
@[stacks 039E "flatness of the target over the base"]
public theorem flat_of_flat_fiberHom_of_surjective {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g]
    [AlgebraicGeometry.Flat (f ≫ g)] [AlgebraicGeometry.Surjective f]
    (hfib : ∀ s : S, AlgebraicGeometry.Flat (fiberHom f g s)) :
    AlgebraicGeometry.Flat g :=
  AlgebraicGeometry.Flat.of_stalkMap g fun y => by
    obtain ⟨x, rfl⟩ := AlgebraicGeometry.Surjective.surj (f := f) y
    exact (flat_stalkMap_of_flat_fiberHom f g hfib x).1

end Stacks.Flatness
