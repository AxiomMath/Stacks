module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Specialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SitePoint

/-!
# Stalks of a presheaf comparable to a constant presheaf

Let `B` be a big étale site containing a scheme `S`, let `U` be an object of the small étale
site of `S` and let `P` be a presheaf of sets on that site. A comparison map `ψ` from the
constant presheaf with value `E` on the localized site `Over U` to the restriction of `P`
attaches to each element of `E` a section of `P` over `U`, hence a germ at every geometric
point of `S` equipped with a lift to `U`. If `ψ` is locally bijective for the localized
topology, that germ map is a bijection `E ≃ P_s`; in particular the stalk is finite as soon as
`E` is, and the specialization map between two such stalks is bijective.

## Main definitions

* `AlgebraicGeometry.constantGerm` — the germ at a geometric point of the section attached to
  an element of `E` by a comparison map from the constant presheaf.

## Main results

* `AlgebraicGeometry.constantPresheafHom_app` — a comparison map out of a constant presheaf is
  determined by its value at the identity of `U`.
* `AlgebraicGeometry.bijective_constantGerm` — a locally bijective comparison map from the
  constant presheaf identifies `E` with the stalk.
* `AlgebraicGeometry.specializationMapOnStalks_constantGerm` — the specialization map carries
  germs of such sections to germs of the same sections.
* `AlgebraicGeometry.finite_etaleStalk_of_bijective_constantGerm` — the stalk is finite when `E`
  is.
* `AlgebraicGeometry.bijective_specializationMapOnStalks_of_constantGerm` — the specialization
  map between two such stalks is bijective.

## References

* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
* [Stacks Project, Section 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : SmallEtale B S hS} {E : Type (u + 1)} {P : (SmallEtale B S hS)ᵒᵖ ⥤ Type (u + 1)}

/-- The germ at a geometric point `s`, through a lift `x` of `s` to `U`, of the section of `P`
over `U` attached to an element of `E` by a comparison map from the constant presheaf. -/
public def constantGerm (s : GeometricPoint S) (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P) (e : E) :
    etaleStalk B S hS s P :=
  (geometricPointSitePoint B S hS s).toPresheafFiber U x P
    (ψ.app (op (Over.mk (𝟙 U))) e)

/-- A comparison map from the constant presheaf with value `E` on `Over U` is determined by its
value at the identity of `U`: on an object `V` it is the restriction along `V.hom`. -/
public theorem constantPresheafHom_app (V : Over U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P) (e : E) :
    ψ.app (op V) e = P.map V.hom.op (ψ.app (op (Over.mk (𝟙 U))) e) :=
  NatTrans.naturality_apply ψ (Over.homMk V.hom (by simp) : V ⟶ Over.mk (𝟙 U)).op e

/-- A comparison map from the constant presheaf on `E` over `U` which is locally bijective
identifies `E` with the stalk of `P` at any geometric point having a lift to `U`. -/
public theorem bijective_constantGerm (s : GeometricPoint S)
    (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P)
    (hinj : Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U) ψ)
    (hsurj : Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U) ψ) :
    Function.Bijective (constantGerm B S hS s x ψ) := by
  let Φ := geometricPointSitePoint B S hS s
  constructor
  · intro e e' heq
    replace heq : Φ.toPresheafFiber U x P (ψ.app (op (Over.mk (𝟙 U))) e) =
      Φ.toPresheafFiber U x P (ψ.app (op (Over.mk (𝟙 U))) e') := heq
    obtain ⟨Y, f, y, -, hfe⟩ := (Φ.toPresheafFiber_eq_iff' U x _ _).1 heq
    have happ : ψ.app (op (Over.mk f)) e = ψ.app (op (Over.mk f)) e' := by
      rwa [constantPresheafHom_app B S hS (Over.mk f) ψ e,
        constantPresheafHom_app B S hS (Over.mk f) ψ e']
    have hmem := hinj.equalizerSieve_mem (X := op (Over.mk f)) e e' happ
    rw [GrothendieckTopology.mem_over_iff] at hmem
    obtain ⟨Z, g, hg, -, -⟩ := Φ.jointly_surjective _ hmem y
    rw [Sieve.overEquiv_iff] at hg
    simpa using hg
  · intro z
    obtain ⟨W, w, c, hc⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) z
    let ZW : Φ.fiber.Elements := Functor.elementsMk Φ.fiber W w
    let ZU : Φ.fiber.Elements := Functor.elementsMk Φ.fiber U x
    let Z : Φ.fiber.Elements := IsCofiltered.min ZW ZU
    let m : Z.1 ⟶ W := (IsCofiltered.minToLeft ZW ZU).1
    let k : Z.1 ⟶ U := (IsCofiltered.minToRight ZW ZU).1
    have hm : Φ.fiber.map m Z.2 = w := (IsCofiltered.minToLeft ZW ZU).2
    have hk : Φ.fiber.map k Z.2 = x := (IsCofiltered.minToRight ZW ZU).2
    have hz : Φ.toPresheafFiber Z.1 Z.2 P (P.map m.op c) = z := by
      rwa [Φ.toPresheafFiber_w_apply m Z.2 P c, hm]
    have hmem := hsurj.imageSieve_mem (U := Over.mk k) (P.map m.op c)
    rw [GrothendieckTopology.mem_over_iff] at hmem
    obtain ⟨Y, g, hg, y, hy⟩ := Φ.jointly_surjective _ hmem Z.2
    rw [Sieve.overEquiv_iff] at hg
    obtain ⟨e, he⟩ := hg
    refine ⟨e, ?_⟩
    have hval : P.map (g ≫ k).op (ψ.app (op (Over.mk (𝟙 U))) e) =
        P.map g.op (P.map m.op c) :=
      (constantPresheafHom_app B S hS (Over.mk (g ≫ k)) ψ e).symm.trans he
    have hgy : Φ.fiber.map (g ≫ k) y = x := by
      rwa [Φ.fiber.map_comp, ConcreteCategory.comp_apply, hy]
    change Φ.toPresheafFiber U x P (ψ.app (op (Over.mk (𝟙 U))) e) = z
    rw [← hgy, ← Φ.toPresheafFiber_w_apply (g ≫ k) y P, hval,
      Φ.toPresheafFiber_w_apply g y P, hy]
    exact hz

/-- The specialization map carries the germ at `s` of the section attached to an element of `E`
to the germ of the same section at the specialized geometric point. -/
public theorem specializationMapOnStalks_constantGerm {s : GeometricPoint S}
    (σ : GeometricSpecialization B S hS s)
    (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P) (e : E) :
    specializationMapOnStalks σ P (constantGerm B S hS s x ψ e) =
      constantGerm B S hS σ.target ((specializationFiberHom σ).app U x) ψ e :=
  specializationMapOnStalks_ι σ P
    (Functor.elementsMk (geometricPointFiber B S hS s) U x)
    (ψ.app (op (Over.mk (𝟙 U))) e)

/-- A locally bijective comparison map from a finite constant presheaf makes the stalk at any
geometric point with a lift to `U` finite. -/
public theorem finite_etaleStalk_of_bijective_constantGerm [Finite E] (s : GeometricPoint S)
    (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P)
    (hinj : Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U) ψ)
    (hsurj : Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U) ψ) :
    Finite (etaleStalk B S hS s P) :=
  (bijective_constantGerm B S hS s x ψ hinj hsurj).finite_iff.1 inferInstance

/-- If a geometric point lifts to an object over which `P` is comparable to a constant presheaf
by a locally bijective map, the specialization map to any specialization of it is bijective. -/
public theorem bijective_specializationMapOnStalks_of_constantGerm {s : GeometricPoint S}
    (σ : GeometricSpecialization B S hS s)
    (x : (geometricPointFiber B S hS s).obj U)
    (ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ P)
    (hinj : Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U) ψ)
    (hsurj : Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U) ψ) :
    Function.Bijective (specializationMapOnStalks σ P) := by
  rw [← Function.Bijective.of_comp_iff _ (bijective_constantGerm B S hS s x ψ hinj hsurj)]
  convert bijective_constantGerm B S hS σ.target ((specializationFiberHom σ).app U x) ψ hinj hsurj
  exact funext (specializationMapOnStalks_constantGerm B S hS σ x ψ)

end AlgebraicGeometry

end
