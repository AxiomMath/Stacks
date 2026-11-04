module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Algebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian

/-!
# Formal objects over a scheme

Let `p : F ⥤ (big fppf site over S)` be a category fibred in groupoids. A *formal object*
of `p` consists of a Noetherian complete local `S`-algebra `R` with finite-type residue
field together with a compatible system of objects of `F`, one over each infinitesimal
thickening `Spec (R / 𝔪 ^ (n + 1))` of the closed point of `Spec R`. Morphisms of formal
objects are compatible families of morphisms of the levels; such a family determines a
unique morphism of the complete local bases, recovered from adic completeness.

Conversely, an object of `F` lying over the spectrum of such a complete local ring
restricts to all of those infinitesimal thickenings, and this restriction is functorial.
A formal object is *effective* when it lies in the essential image of that restriction
functor, i.e. when it comes, up to isomorphism, from a genuine object over a complete
local base.

## Main definitions

* `Deformation.Artin.FormalBase` — a Noetherian complete local ring with a structure
  morphism to the base scheme and finite-type residue field.
* `Deformation.Artin.FormalObject` — a formal object of `p`.
* `Deformation.Artin.FormalObject.Hom` — a compatible family of morphisms of formal
  objects, with its componentwise category structure.
* `Deformation.Artin.IsCompleteLocalObject` — the objects of `F` lying over spectra of
  Noetherian complete local rings with finite-type residue field.
* `Deformation.Artin.CompleteLocalObjects` — those objects, with morphisms restricted to
  the ones inducing local maps of the complete local bases.
* `Deformation.Artin.IsApproximationFunctor` — the equations characterizing restriction to
  all infinitesimal thickenings.
* `Deformation.Artin.FormalObject.IsEffective` — membership in the essential image of the
  approximation functor.

## Main results

* `Deformation.Artin.FormalObject.Hom.ext` gives componentwise extensionality, and
  `Deformation.Artin.FormalObject.Hom.baseMapData` produces the unique induced map of
  complete local bases.
* `Deformation.Artin.approximationFunctorData` constructs the restriction functor from
  complete local objects to formal objects, together with the equations specifying its
  restrictions and its action on morphisms.

## References

* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

/-! ### Formal objects and their morphisms -/

section

open AlgebraicGeometry CategoryTheory
open IsLocalRing

universe u v w

/-- A Noetherian complete local ring over `S` whose residue field is of finite type over
`S`. -/
public structure FormalBase (S : Scheme.{u}) where
  /-- The underlying ring. -/
  R : Type u
  [commRing : CommRing R]
  [localRing : IsLocalRing R]
  /-- The ring is Noetherian. -/
  noetherian : IsNoetherianRing R
  /-- The ring is complete in its maximal-ideal-adic topology. -/
  complete : IsAdicComplete (maximalIdeal R) R
  /-- Its structure morphism to `S`. -/
  toS : Spec (.of R) ⟶ S
  /-- The residue-field morphism is locally of finite type. -/
  residueLocallyFiniteType :
    LocallyOfFiniteType (adicThickeningι R (maximalIdeal R) 0 ≫ toS)
  /-- The residue-field morphism is quasi-compact. -/
  residueQuasiCompact :
    QuasiCompact (adicThickeningι R (maximalIdeal R) 0 ≫ toS)

attribute [instance] FormalBase.commRing FormalBase.localRing

namespace FormalBase

/-- The spectrum of the quotient by the `(n + 1)`-st power of the maximal ideal. -/
public abbrev truncation {S : Scheme.{u}} (A : FormalBase S) (n : ℕ) : Scheme.{u} :=
  adicThickening A.R (maximalIdeal A.R) n

/-- The structure morphism of an infinitesimal thickening to `S`. -/
public def truncationToS {S : Scheme.{u}} (A : FormalBase S) (n : ℕ) :
    A.truncation n ⟶ S :=
  adicThickeningι A.R (maximalIdeal A.R) n ≫ A.toS

/-- The inclusion of one infinitesimal thickening in the next. -/
public def truncationSucc {S : Scheme.{u}} (A : FormalBase S) (n : ℕ) :
    A.truncation n ⟶ A.truncation (n + 1) :=
  adicThickeningSucc A.R (maximalIdeal A.R) n

/-- The inclusions of successive infinitesimal thickenings are maps over `S`. -/
@[reassoc (attr := simp)]
public theorem truncationSucc_toS {S : Scheme.{u}} (A : FormalBase S) (n : ℕ) :
    A.truncationSucc n ≫ A.truncationToS (n + 1) = A.truncationToS n := by
  show adicThickeningSucc A.R (maximalIdeal A.R) n ≫
      (adicThickeningι A.R (maximalIdeal A.R) (n + 1) ≫ A.toS) =
    adicThickeningι A.R (maximalIdeal A.R) n ≫ A.toS
  rw [← Category.assoc, adicThickeningSucc_ι]

end FormalBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An infinitesimal thickening regarded as an object of the chosen big fppf site. -/
public def truncationOver (A : FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n)) (n : ℕ) :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := ⟨A.truncation n, contains n⟩)
    (Y := B.obj hS) (A.truncationToS n))

/-- The canonical inclusion between successive infinitesimal thickenings in the site. -/
public def truncationOverSucc (A : FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n)) (n : ℕ) :
    truncationOver B S hS A contains n ⟶ truncationOver B S hS A contains (n + 1) := by
  refine Over.homMk
    (ObjectProperty.homMk (X := ⟨A.truncation n, contains n⟩)
      (Y := ⟨A.truncation (n + 1), contains (n + 1)⟩)
      (A.truncationSucc n)) ?_
  exact ObjectProperty.hom_ext _ (A.truncationSucc_toS n)

/-- A formal object of a category over the big fppf site of `S`. -/
@[stacks 07X4 "formal objects"]
public structure FormalObject {F : Type v} [Category.{w} F]
    (p : F ⥤ BigFppfOver B S hS) where
  /-- The complete local algebra underlying the formal object. -/
  base : FormalBase S
  /-- Each infinitesimal thickening belongs to the chosen big fppf site. -/
  contains : ∀ n, B.Contains (base.truncation n)
  /-- The object at each infinitesimal level. -/
  level : ℕ → F
  /-- The level lies over its prescribed infinitesimal thickening. -/
  level_eq : ∀ n, p.obj (level n) = truncationOver B S hS base contains n
  /-- The transition morphism from one level to the next. -/
  transition : ∀ n, level n ⟶ level (n + 1)
  /-- The transition lies over the canonical closed immersion. -/
  transition_lift : ∀ n, p.IsHomLift
    (truncationOverSucc B S hS base contains n) (transition n)

namespace FormalObject

variable {B S hS} {F : Type v} [Category.{w} F]
    {p : F ⥤ BigFppfOver B S hS}

/-- A compatible family of morphisms between formal objects. -/
@[stacks 07X4 "morphisms"]
public structure Hom (X Y : FormalObject B S hS p) where
  /-- The morphism at each infinitesimal level. -/
  app : ∀ n, X.level n ⟶ Y.level n
  /-- The level maps form a compatible family. -/
  naturality : ∀ n, X.transition n ≫ app (n + 1) = app n ≫ Y.transition n

/-- Morphisms of formal objects are equal when all their level maps agree. -/
@[ext]
public theorem Hom.ext {X Y : FormalObject B S hS p} {f g : Hom X Y}
    (happ : ∀ n, f.app n = g.app n) : f = g := by
  cases f; cases g; cases funext happ; rfl

/-- The category of formal objects, with componentwise identity and composition. -/
public instance : Category (FormalObject B S hS p) where
  Hom := Hom
  id X := ⟨fun _ ↦ 𝟙 _, fun n ↦ by simp⟩
  comp f g := ⟨fun n ↦ f.app n ≫ g.app n, fun n ↦ by
    rw [← Category.assoc, f.naturality n, Category.assoc, g.naturality n,
      ← Category.assoc]⟩
  id_comp f := by apply Hom.ext; intro n; simp
  comp_id f := by apply Hom.ext; intro n; simp
  assoc f g h := by apply Hom.ext; intro n; simp [Category.assoc]

/-- Evaluation of a formal object and its morphisms at the `n`-th thickening. -/
@[implicit_reducible]
public def evaluation (n : ℕ) : FormalObject B S hS p ⥤ F where
  obj X := X.level n
  map f := f.app n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The compatibility condition for a map between the complete local bases to be induced
by a morphism of formal objects. -/
public def Hom.IsBaseMap {X Y : FormalObject B S hS p} (f : Hom X Y)
    (a : Spec (.of X.base.R) ⟶ Spec (.of Y.base.R)) : Prop :=
  a ≫ Y.base.toS = X.base.toS ∧
    ∀ n,
      (eqToHom (X.level_eq n).symm ≫ p.map (f.app n) ≫
        eqToHom (Y.level_eq n)).left.hom ≫
        adicThickeningι Y.base.R (maximalIdeal Y.base.R) n =
        adicThickeningι X.base.R (maximalIdeal X.base.R) n ≫ a

/-- A compatible family induces a unique map between its complete local bases. -/
@[stacks 07X4 "the induced map of complete bases"]
public noncomputable def Hom.baseMapData {X Y : FormalObject B S hS p} (f : Hom X Y) :
    {a : Spec (.of X.base.R) ⟶ Spec (.of Y.base.R) //
      f.IsBaseMap a ∧ ∀ b, f.IsBaseMap b → b = a} := by
  let R : Type u := X.base.R
  let tmap : ∀ n, X.base.truncation n ⟶ Y.base.truncation n := fun n ↦
    (eqToHom (X.level_eq n).symm ≫ p.map (f.app n) ≫
      eqToHom (Y.level_eq n)).left.hom
  have tmap_toS (n : ℕ) :
      tmap n ≫ Y.base.truncationToS n = X.base.truncationToS n := by
    simpa only [tmap, FormalBase.truncationToS, truncationOver,
      Over.mk_hom, ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom,
      Category.assoc] using congrArg (fun t ↦ t.hom)
        (eqToHom (X.level_eq n).symm ≫ p.map (f.app n) ≫ eqToHom (Y.level_eq n)).w
  have tmap_compat (n : ℕ) :
      X.base.truncationSucc n ≫ tmap (n + 1) =
        tmap n ≫ Y.base.truncationSucc n := by
    let := X.transition_lift n; let := Y.transition_lift n
    have hX := IsHomLift.fac p (truncationOverSucc B S hS X.base X.contains n)
      (X.transition n)
    have hY := IsHomLift.fac p (truncationOverSucc B S hS Y.base Y.contains n)
      (Y.transition n)
    have h :
        truncationOverSucc B S hS X.base X.contains n ≫
          (eqToHom (X.level_eq (n + 1)).symm ≫ p.map (f.app (n + 1)) ≫
            eqToHom (Y.level_eq (n + 1))) =
        (eqToHom (X.level_eq n).symm ≫ p.map (f.app n) ≫
            eqToHom (Y.level_eq n)) ≫
          truncationOverSucc B S hS Y.base Y.contains n := by
      rw [hX, hY]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      simp only [← Category.assoc, ← Functor.map_comp, f.naturality n]
    have h' := congrArg (fun g ↦ (BigFppfOver.toScheme B S hS).map g) h
    change X.base.truncationSucc n ≫ tmap (n + 1) =
      tmap n ≫ Y.base.truncationSucc n at h'
    exact h'
  let rmap (n : ℕ) : Y.base.R →+* R ⧸ maximalIdeal R ^ (n + 1) :=
    (Spec.preimage (tmap n)).hom.comp
      (Ideal.Quotient.mk (maximalIdeal Y.base.R ^ (n + 1)))
  have rmap_compat (n : ℕ) :
      (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))).comp
        (rmap (n + 1)) = rmap n := by
    have h := congrArg Spec.preimage (tmap_compat n)
    simp only [Spec.preimage_comp] at h
    apply RingHom.ext; intro x
    have hx := congrArg (fun φ ↦ φ.hom
      ((Ideal.Quotient.mk (maximalIdeal Y.base.R ^ (n + 2))) x)) h
    simpa [rmap, FormalBase.truncationSucc, adicThickeningSucc] using hx
  have ext_scheme : ∀ {T : Scheme.{u}} (a b : Spec (.of R) ⟶ T),
      (∀ n, adicThickeningι R (maximalIdeal R) n ≫ a =
        adicThickeningι R (maximalIdeal R) n ≫ b) → a = b := by
    intro T a b h
    let : IsAdicComplete (maximalIdeal R) R := X.base.complete
    have : Nontrivial (R ⧸ maximalIdeal R ^ (0 + 1)) :=
      Ideal.Quotient.nontrivial_iff.mpr (by simpa only [zero_add, pow_one] using
        (maximalIdeal.isMaximal R).ne_top)
    have : IsLocalRing (R ⧸ maximalIdeal R ^ (0 + 1)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have hcp : adicThickeningι R (maximalIdeal R) 0
        (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1))) = closedPoint R := by
      let : IsLocalHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      exact Spec_closedPoint
    have hab : a (closedPoint R) = b (closedPoint R) := by
      have h0 := congrArg (fun e ↦ e (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1)))) (h 0)
      change a ((adicThickeningι R (maximalIdeal R) 0)
        (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1)))) =
        b ((adicThickeningι R (maximalIdeal R) 0)
        (closedPoint (R ⧸ maximalIdeal R ^ (0 + 1)))) at h0
      simpa only [hcp] using h0
    obtain ⟨_, ⟨U, hU, rfl⟩, haU, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (a (closedPoint R))) isOpen_univ
    change IsAffineOpen U at hU
    let ia := (Scheme.preimage_eq_top_of_closedPoint_mem (U := U) a haU).ge
    let ib := (Scheme.preimage_eq_top_of_closedPoint_mem (U := U) b (hab ▸ haU)).ge
    let aU : Spec (.of R) ⟶ Spec Γ(T, U) :=
      (Spec (.of R)).isoSpec.hom ≫ Spec.map (a.appLE U ⊤ ia)
    let bU : Spec (.of R) ⟶ Spec Γ(T, U) :=
      (Spec (.of R)).isoSpec.hom ≫ Spec.map (b.appLE U ⊤ ib)
    have ha : aU ≫ hU.fromSpec = a := by
      dsimp [aU]; rw [Category.assoc, hU.SpecMap_appLE_fromSpec a (isAffineOpen_top _) ia]
      simp [IsAffineOpen.fromSpec_top]
    have hb : bU ≫ hU.fromSpec = b := by
      dsimp [bU]; rw [Category.assoc, hU.SpecMap_appLE_fromSpec b (isAffineOpen_top _) ib]
      simp [IsAffineOpen.fromSpec_top]
    have habU : ∀ n, adicThickeningι R (maximalIdeal R) n ≫ aU =
        adicThickeningι R (maximalIdeal R) n ≫ bU := by
      intro n; apply (cancel_mono hU.fromSpec).mp
      simpa [Category.assoc, ha, hb] using h n
    obtain ⟨φ, hφ⟩ := Spec.map_surjective aU
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective bU
    have heq : φ = ψ := by
      apply CommRingCat.hom_ext
      have hs : StrictMono (fun n : ℕ ↦ n + 1) := fun _ _ hij ↦ Nat.add_lt_add_right hij 1
      apply DFunLike.coe_injective
      apply IsHausdorff.StrictMono.funext' (maximalIdeal R) hs
      intro n x
      have hn := habU n
      rw [← hφ, ← hψ] at hn
      have hr := congrArg Spec.preimage hn
      have hr' := congrArg (fun k ↦ k.hom x) hr
      simpa [Spec.preimage_comp, adicThickeningι] using hr'
    rw [← ha, ← hb, ← hφ, ← hψ, heq]
  letI : IsAdicComplete (maximalIdeal R) R := X.base.complete
  have hs : StrictMono (fun n : ℕ ↦ n + 1) := fun _ _ hij ↦ Nat.add_lt_add_right hij 1
  let ringMap : Y.base.R →+* R :=
    IsAdicComplete.StrictMono.liftRingHom (I := maximalIdeal R)
      (ha := hs) (f := rmap) (hf := rmap_compat _)
  have ringMap_mod (n : ℕ) :
      (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))).comp ringMap = rmap n := by
    simpa only [ringMap] using (IsAdicComplete.StrictMono.mk_comp_liftRingHom
      (I := maximalIdeal R) (ha := hs) (f := rmap) (hf := rmap_compat _) (n := n))
  let a : Spec (.of R) ⟶ Spec (.of Y.base.R) := Spec.map (CommRingCat.ofHom ringMap)
  have a_trunc (n : ℕ) :
      tmap n ≫ adicThickeningι Y.base.R (maximalIdeal Y.base.R) n =
        adicThickeningι R (maximalIdeal R) n ≫ a := by
    dsimp [a]
    rw [adicThickeningι, adicThickeningι, ← Spec.map_comp,
      ← Spec.map_preimage (tmap n), ← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    simpa [rmap] using (ringMap_mod n).symm
  refine ⟨a, ?_, ?_⟩
  · constructor
    · apply ext_scheme
      intro n
      calc
        adicThickeningι X.base.R (maximalIdeal X.base.R) n ≫
            (a ≫ Y.base.toS) =
          tmap n ≫ Y.base.truncationToS n := by
            rw [← Category.assoc, ← a_trunc n]
            rfl
        _ = X.base.truncationToS n := tmap_toS n
        _ = adicThickeningι X.base.R (maximalIdeal X.base.R) n ≫
            X.base.toS := rfl
    · exact a_trunc
  · intro b hb; apply ext_scheme; intro n
    exact (hb.2 n).symm.trans (a_trunc n)

/-- The map of complete local bases induced by a morphism of formal objects. -/
public noncomputable def Hom.baseMap {X Y : FormalObject B S hS p} (f : Hom X Y) :
    Spec (.of X.base.R) ⟶ Spec (.of Y.base.R) := f.baseMapData.1

/-- The induced map of complete local bases satisfies the compatibility conditions. -/
public theorem Hom.baseMap_spec {X Y : FormalObject B S hS p} (f : Hom X Y) :
    f.IsBaseMap f.baseMap := f.baseMapData.2.1

/-- The induced map of complete local bases is the only compatible one. -/
public theorem Hom.baseMap_unique {X Y : FormalObject B S hS p} (f : Hom X Y)
    (a : Spec (.of X.base.R) ⟶ Spec (.of Y.base.R)) (ha : f.IsBaseMap a) :
    a = f.baseMap := f.baseMapData.2.2 a ha

end FormalObject

end

/-! ### From complete local objects to formal objects -/

section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : Type v} [Category.{w} F]
    (p : F ⥤ BigFppfOver B S hS)

/-- A complete local spectrum, regarded as an object of the big fppf site over `S`. -/
public def baseOver (A : FormalBase S)
    (hA : B.Contains (Spec (.of A.R))) : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj hA) (Y := B.obj hS) A.toS)

/-- The property defining the full subcategory on objects over suitable complete
local spectra. -/
public def IsCompleteLocalObject : ObjectProperty F := fun x ↦
  ∃ (A : FormalBase S) (hA : B.Contains (Spec (.of A.R))),
    p.obj x = baseOver B S hS A hA

/-- Objects over Noetherian complete local rings whose residue fields are of
finite type over `S`, initially with all morphisms. -/
public abbrev CompleteLocalObjectsFull :=
  (IsCompleteLocalObject B S hS p).FullSubcategory

/-- A chosen complete local base for an object of `CompleteLocalObjectsFull`. -/
public noncomputable def chosenBase
    (x : CompleteLocalObjectsFull B S hS p) : FormalBase S :=
  Classical.choose x.property

/-- The spectrum of the chosen complete local base lies in the chosen big fppf site. -/
public theorem chosenContains
    (x : CompleteLocalObjectsFull B S hS p) :
    B.Contains (Spec (.of (chosenBase B S hS p x).R)) :=
  Classical.choose (Classical.choose_spec x.property)

/-- The object lies over the spectrum of its chosen complete local base. -/
public theorem chosenBase_eq
    (x : CompleteLocalObjectsFull B S hS p) :
    p.obj x.1 = baseOver B S hS (chosenBase B S hS p x)
      (chosenContains B S hS p x) :=
  Classical.choose_spec (Classical.choose_spec x.property)

/-- The map on complete local bases underlying a morphism of objects. -/
public def baseMap {x y : CompleteLocalObjectsFull B S hS p} (f : x ⟶ y) :
    Spec (.of (chosenBase B S hS p x).R) ⟶
      Spec (.of (chosenBase B S hS p y).R) :=
  (BigFppfOver.toScheme B S hS).map
    (eqToHom (chosenBase_eq B S hS p x).symm ≫ p.map f.1 ≫
      eqToHom (chosenBase_eq B S hS p y))

/-- Morphisms that preserve the closed points of their complete local bases. -/
public def IsLocalBaseMap {x y : CompleteLocalObjectsFull B S hS p}
    (f : x ⟶ y) : Prop :=
  baseMap B S hS p f (closedPoint (chosenBase B S hS p x).R) =
    closedPoint (chosenBase B S hS p y).R

/-- The identity induces the identity of complete local bases. -/
public theorem baseMap_id (x : CompleteLocalObjectsFull B S hS p) :
    baseMap B S hS p (𝟙 x) = 𝟙 _ := by
  show (BigFppfOver.toScheme B S hS).map
    (eqToHom (chosenBase_eq B S hS p x).symm ≫
      p.map (𝟙 x.1) ≫ eqToHom (chosenBase_eq B S hS p x)) = 𝟙 _
  simp

/-- The induced map of complete local bases is compatible with composition. -/
public theorem baseMap_comp {x y z : CompleteLocalObjectsFull B S hS p}
    (f : x ⟶ y) (g : y ⟶ z) :
    baseMap B S hS p (f ≫ g) =
      baseMap B S hS p f ≫ baseMap B S hS p g := by
  show (BigFppfOver.toScheme B S hS).map
      (eqToHom (chosenBase_eq B S hS p x).symm ≫
        p.map (f.1 ≫ g.1) ≫ eqToHom (chosenBase_eq B S hS p z)) =
    (BigFppfOver.toScheme B S hS).map
      (eqToHom (chosenBase_eq B S hS p x).symm ≫ p.map f.1 ≫
        eqToHom (chosenBase_eq B S hS p y)) ≫
    (BigFppfOver.toScheme B S hS).map
      (eqToHom (chosenBase_eq B S hS p y).symm ≫ p.map g.1 ≫
        eqToHom (chosenBase_eq B S hS p z))
  simp only [← Functor.map_comp]
  simp [Category.assoc]

/-- The multiplicative morphism property of local base maps. -/
public def localBaseMaps : MorphismProperty (CompleteLocalObjectsFull B S hS p) :=
  fun _ _ f ↦ IsLocalBaseMap B S hS p f

/-- Local base maps contain the identities and are closed under composition. -/
public instance : (localBaseMaps B S hS p).IsMultiplicative where
  id_mem x := by
    change baseMap B S hS p (𝟙 x) (closedPoint _) = closedPoint _
    rw [baseMap_id]
    rfl
  comp_mem f g hf hg := by
    change IsLocalBaseMap B S hS p (f ≫ g)
    change IsLocalBaseMap B S hS p f at hf
    change IsLocalBaseMap B S hS p g at hg
    rw [IsLocalBaseMap, baseMap_comp]
    change (baseMap B S hS p g) ((baseMap B S hS p f) (closedPoint _)) = _
    rw [hf, hg]

/-- The category of objects over suitable complete local rings, with local
morphisms of their bases. -/
public abbrev CompleteLocalObjects := WideSubcategory (localBaseMaps B S hS p)

/-- The equations which characterize restriction to all infinitesimal thickenings.
The maps to the original objects are Cartesian, commute with the transitions,
and are natural for morphisms in the full subcategory. -/
public def IsApproximationFunctor
    (G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p) : Prop :=
  ∃ (r : ∀ (x : CompleteLocalObjects B S hS p) (n : ℕ), (G.obj x).level n ⟶ x.obj.1),
    ∃ (hbase : ∀ x, (G.obj x).base = chosenBase B S hS p x.obj),
    (∀ x n, p.IsCartesian (p.map (r x n)) (r x n)) ∧
    (∀ x n, (G.obj x).transition n ≫ r x (n + 1) = r x n) ∧
    (∀ (x y : CompleteLocalObjects B S hS p) (f : x ⟶ y) (n : ℕ),
      (G.map f).app n ≫ r y n = r x n ≫ f.1.1) ∧
    (∀ x n,
      (BigFppfOver.toScheme B S hS).map
          (eqToHom ((G.obj x).level_eq n).symm ≫ p.map (r x n) ≫
            eqToHom (chosenBase_eq B S hS p x.obj)) =
        adicThickeningι (G.obj x).base.R
          (maximalIdeal (G.obj x).base.R) n ≫
          eqToHom (congrArg (fun A : FormalBase S ↦ Spec (.of A.R))
          (hbase x)))

/-- The `n`-th infinitesimal thickening of a complete local base, in the site. -/
public abbrev restrictionBase (A : FormalBase S)
    (contains : ∀ n, B.Contains (A.truncation n)) (n : ℕ) :
    BigFppfOver B S hS :=
  truncationOver B S hS A contains n

/-- The canonical map from an infinitesimal thickening to the complete local base,
viewed in the site. -/
public noncomputable def restrictionToBase (A : FormalBase S)
    (hA : B.Contains (Spec (.of A.R))) (contains : ∀ n, B.Contains (A.truncation n))
    (n : ℕ) : restrictionBase B S hS A contains n ⟶ baseOver B S hS A hA := by
  change truncationOver B S hS A contains n ⟶ baseOver B S hS A hA
  refine Over.homMk (ObjectProperty.homMk
    (X := ⟨A.truncation n, contains n⟩) (Y := B.obj hA)
    (adicThickeningι A.R (maximalIdeal A.R) n)) ?_
  apply ObjectProperty.hom_ext
  change adicThickeningι A.R (maximalIdeal A.R) n ≫ A.toS = _
  rfl

/-- The map induced by a local homomorphism on the quotients by the `(n + 1)`-st powers
of the maximal ideals. -/
public noncomputable def localQuotientMap
    {R T : Type u} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
    (f : R →+* T) [IsLocalHom f] (n : ℕ) :
    R ⧸ maximalIdeal R ^ (n + 1) →+* T ⧸ maximalIdeal T ^ (n + 1) := by
  have hpow : (maximalIdeal R).map f ^ (n + 1) ≤ maximalIdeal T ^ (n + 1) :=
    pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le f) _
  have h : maximalIdeal R ^ (n + 1) ≤ (maximalIdeal T ^ (n + 1)).comap f := by
    have hpow' : (maximalIdeal R ^ (n + 1)).map f ≤ maximalIdeal T ^ (n + 1) := by
      simpa only [Ideal.map_pow] using hpow
    exact (Ideal.map_le_iff_le_comap).mp hpow'
  exact Ideal.quotientMap _ f h

/-- The quotient map intertwines `localQuotientMap f n` with `f`. -/
public theorem localQuotientMap_comp_mk
    {R T : Type u} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
    (f : R →+* T) [IsLocalHom f] (n : ℕ) :
    (localQuotientMap f n).comp (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) =
      (Ideal.Quotient.mk (maximalIdeal T ^ (n + 1))).comp f := by
  unfold localQuotientMap
  exact Ideal.quotientMap_comp_mk _

/-- The construction sends the identity to the identity. -/
public theorem localQuotientMap_id (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) : localQuotientMap (RingHom.id R) n = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  rw [localQuotientMap_comp_mk]
  simp

/-- The construction is compatible with composition. -/
public theorem localQuotientMap_comp
    {R T U : Type u} [CommRing R] [IsLocalRing R]
    [CommRing T] [IsLocalRing T] [CommRing U] [IsLocalRing U]
    (f : R →+* T) [IsLocalHom f] (g : T →+* U) [IsLocalHom g] (n : ℕ) :
    localQuotientMap (g.comp f) n =
      (localQuotientMap g n).comp (localQuotientMap f n) := by
  apply Ideal.Quotient.ringHom_ext
  rw [localQuotientMap_comp_mk, RingHom.comp_assoc,
    localQuotientMap_comp_mk, ← RingHom.comp_assoc,
    ← localQuotientMap_comp_mk g n, RingHom.comp_assoc]

/-- If the spectrum of a complete local base lies in the chosen big fppf site, then so
does each of its infinitesimal thickenings. -/
public theorem truncationContains (A : FormalBase S)
    (hA : B.Contains (Spec (.of A.R))) (n : ℕ) : B.Contains (A.truncation n) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (R := A.R) (A := A.R ⧸ maximalIdeal A.R ^ (n + 1)) hA
    ((Cardinal.mk_le_of_surjective (Ideal.Quotient.mk_surjective :
      Function.Surjective (Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1))))).trans
        (le_max_right Cardinal.aleph0 (Cardinal.mk A.R)))

/-- The restriction of a complete local object to the `n`-th infinitesimal thickening. -/
public noncomputable def restrictionLevel
    (hp : p.IsFiberedInGroupoids) (x : CompleteLocalObjectsFull B S hS p) (n : ℕ) :
    F := by
  letI : p.IsFibered := Functor.IsFiberedInGroupoids.isFibered hp
  exact Functor.IsPreFibered.pullbackObj
    (chosenBase_eq B S hS p x)
    (restrictionToBase B S hS (chosenBase B S hS p x)
      (chosenContains B S hS p x)
      (fun k ↦ truncationContains B S (chosenBase B S hS p x)
        (chosenContains B S hS p x) k) n)

/-- The cartesian map from a restriction to the original complete local object. -/
public noncomputable def restrictionMap
    (hp : p.IsFiberedInGroupoids) (x : CompleteLocalObjectsFull B S hS p) (n : ℕ) :
    restrictionLevel B S hS p hp x n ⟶ x.1 := by
  letI : p.IsFibered := Functor.IsFiberedInGroupoids.isFibered hp
  exact Functor.IsPreFibered.pullbackMap
    (chosenBase_eq B S hS p x)
    (restrictionToBase B S hS (chosenBase B S hS p x)
      (chosenContains B S hS p x)
      (fun k ↦ truncationContains B S (chosenBase B S hS p x)
        (chosenContains B S hS p x) k) n)

/-- The restriction lies over the `n`-th infinitesimal thickening. -/
public theorem restrictionLevel_eq
    (hp : p.IsFiberedInGroupoids) (x : CompleteLocalObjectsFull B S hS p) (n : ℕ) :
    p.obj (restrictionLevel B S hS p hp x n) =
      truncationOver B S hS (chosenBase B S hS p x)
        (fun k ↦ truncationContains B S (chosenBase B S hS p x)
          (chosenContains B S hS p x) k) n := by
  let : p.IsFibered := Functor.IsFiberedInGroupoids.isFibered hp
  exact Functor.IsPreFibered.pullbackObj_proj
    (chosenBase_eq B S hS p x)
    (restrictionToBase B S hS (chosenBase B S hS p x)
      (chosenContains B S hS p x)
      (fun k ↦ truncationContains B S (chosenBase B S hS p x)
        (chosenContains B S hS p x) k) n)

/-- The maps to the complete local base are compatible with the inclusions of
successive infinitesimal thickenings. -/
public theorem restrictionToBase_succ (A : FormalBase S)
    (hA : B.Contains (Spec (.of A.R))) (contains : ∀ n, B.Contains (A.truncation n))
    (n : ℕ) :
    truncationOverSucc B S hS A contains n ≫
      restrictionToBase B S hS A hA contains (n + 1) =
      restrictionToBase B S hS A hA contains n := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  dsimp only [restrictionToBase, truncationOverSucc,
    truncationOver, baseOver, Over.homMk, ObjectProperty.homMk]
  show adicThickeningSucc A.R (maximalIdeal A.R) n ≫
      adicThickeningι A.R (maximalIdeal A.R) (n + 1) =
    adicThickeningι A.R (maximalIdeal A.R) n
  rw [adicThickeningSucc_ι]

/-- The transition morphism between successive restrictions, together with the facts that
it lies over the canonical inclusion and commutes with the cartesian maps. -/
public noncomputable def restrictionTransitionData
    (hp : p.IsFiberedInGroupoids) (x : CompleteLocalObjectsFull B S hS p) (n : ℕ) :
    {t : restrictionLevel B S hS p hp x n ⟶
      restrictionLevel B S hS p hp x (n + 1) //
      p.IsHomLift (truncationOverSucc B S hS
        (chosenBase B S hS p x)
        (fun k ↦ truncationContains B S (chosenBase B S hS p x)
          (chosenContains B S hS p x) k) n) t ∧
        t ≫ restrictionMap B S hS p hp x (n + 1) =
          restrictionMap B S hS p hp x n} := by
  let A := chosenBase B S hS p x
  let ha := chosenContains B S hS p x
  let contains : ∀ k, B.Contains (A.truncation k) := fun k ↦ truncationContains B S A ha k
  let fn := restrictionToBase B S hS A ha contains n
  let fs := restrictionToBase B S hS A ha contains (n + 1)
  let s := truncationOverSucc B S hS A contains n
  let r := restrictionMap B S hS p hp x n
  let rs := restrictionMap B S hS p hp x (n + 1)
  let hn := restrictionLevel_eq B S hS p hp x n
  let hs := restrictionLevel_eq B S hS p hp x (n + 1)
  let hb := chosenBase_eq B S hS p x
  let q := eqToHom hn ≫ s ≫ eqToHom hs.symm
  have hbase : s ≫ fs = fn := by
    simpa [A, ha, contains, fs, fn, s] using
      restrictionToBase_succ B S hS A ha contains n
  letI : p.IsFibered := Functor.IsFiberedInGroupoids.isFibered hp
  haveI : p.IsHomLift fn r := by
    change p.IsHomLift fn (Functor.IsPreFibered.pullbackMap hb fn)
    infer_instance
  haveI : p.IsHomLift fs rs := by
    change p.IsHomLift fs (Functor.IsPreFibered.pullbackMap hb fs)
    infer_instance
  have hcomm : q ≫ p.map rs = p.map r := by
    calc
      q ≫ p.map rs = eqToHom hn ≫ s ≫ fs ≫ eqToHom hb.symm := by
        change (eqToHom hn ≫ s ≫ eqToHom hs.symm) ≫ p.map rs = _
        rw [IsHomLift.fac' p fs rs]
        simp [Category.assoc]
      _ = eqToHom hn ≫ fn ≫ eqToHom hb.symm := by
        simpa [Category.assoc] using
          congrArg (fun g ↦ eqToHom hn ≫ g ≫ eqToHom hb.symm) hbase
      _ = p.map r := (IsHomLift.fac' p fn r).symm
  have hex : ∃ t, p.map t = q ∧ t ≫ rs = r :=
    (hp.unique_lift rs r q hcomm).exists
  let t := Classical.choose hex
  have ht := Classical.choose_spec hex
  refine ⟨t, ?_, ht.2⟩
  apply IsHomLift.of_fac p s t hn hs
  rw [ht.1]
  simp [q]

/-- The transition morphism between successive restrictions. -/
public noncomputable def restrictionTransition
    (hp : p.IsFiberedInGroupoids) (x : CompleteLocalObjectsFull B S hS p) (n : ℕ) :
    restrictionLevel B S hS p hp x n ⟶ restrictionLevel B S hS p hp x (n + 1) :=
  (restrictionTransitionData B S hS p hp x n).1

/-- The induced map of complete local bases is a map over `S`. -/
public theorem baseMap_toS {x y : CompleteLocalObjectsFull B S hS p}
    (f : x ⟶ y) :
    baseMap B S hS p f ≫ (chosenBase B S hS p y).toS =
      (chosenBase B S hS p x).toS := by
  let e := eqToHom (chosenBase_eq B S hS p x).symm ≫
      p.map f.1 ≫ eqToHom (chosenBase_eq B S hS p y)
  have he := congrArg (fun g ↦ B.inclusion.map g) (Over.w e)
  simpa [e, baseMap, BigFppfOver.toScheme,
    BigFppfOver.forget, baseOver] using he

/-- The ring homomorphism underlying the induced map of complete local bases. -/
public noncomputable def baseRingMap {x y : CompleteLocalObjectsFull B S hS p}
    (f : x ⟶ y) : (chosenBase B S hS p y).R →+* (chosenBase B S hS p x).R :=
  (Spec.homEquiv (R := CommRingCat.of (chosenBase B S hS p y).R)
    (S := CommRingCat.of (chosenBase B S hS p x).R) (baseMap B S hS p f)).hom

/-- The induced map of complete local bases is the spectrum of `baseRingMap`. -/
public theorem baseMap_eq_SpecMap {x y : CompleteLocalObjectsFull B S hS p}
    (f : x ⟶ y) :
    Spec.map (CommRingCat.ofHom (baseRingMap B S hS p f)) = baseMap B S hS p f := by
  simp [baseRingMap]

/-- The identity induces the identity ring homomorphism of complete local bases. -/
public theorem baseRingMap_id (x : CompleteLocalObjectsFull B S hS p) :
    baseRingMap B S hS p (𝟙 x) = RingHom.id _ := by
  simp [baseRingMap, baseMap_id]

/-- The induced ring homomorphism is compatible with composition. -/
public theorem baseRingMap_comp {x y z : CompleteLocalObjectsFull B S hS p}
    (f : x ⟶ y) (g : y ⟶ z) :
    baseRingMap B S hS p (f ≫ g) =
      (baseRingMap B S hS p f).comp (baseRingMap B S hS p g) := by
  simp [baseRingMap, baseMap_comp]

/-- A morphism preserving closed points induces a local ring homomorphism. -/
public theorem baseRingMap_isLocal {x y : CompleteLocalObjectsFull B S hS p}
    (f : x ⟶ y) (hf : IsLocalBaseMap B S hS p f) :
    IsLocalHom (baseRingMap B S hS p f) := by
  apply (IsLocalRing.isLocalHom_iff_comap_closedPoint (baseRingMap B S hS p f)).2
  change baseMap B S hS p f
    (closedPoint (chosenBase B S hS p x).R) =
      closedPoint (chosenBase B S hS p y).R at hf
  rw [← baseMap_eq_SpecMap B S hS p f] at hf
  have hcpD := congrArg
    (specOrderIsoPrimeSpectrum (CommRingCat.of (chosenBase B S hS p y).R)) hf
  exact congrArg
    (fun z : (PrimeSpectrum (chosenBase B S hS p y).R)ᵒᵈ ↦ OrderDual.ofDual z) hcpD

/-- The map of `n`-th infinitesimal thickenings induced by a morphism of complete local
objects preserving closed points. -/
public noncomputable def restrictionBaseMap
    {x y : CompleteLocalObjectsFull B S hS p} (f : x ⟶ y)
    (hf : IsLocalBaseMap B S hS p f) (n : ℕ) :
    truncationOver B S hS (chosenBase B S hS p x)
      (fun k ↦ truncationContains B S (chosenBase B S hS p x)
        (chosenContains B S hS p x) k) n ⟶
    truncationOver B S hS (chosenBase B S hS p y)
      (fun k ↦ truncationContains B S (chosenBase B S hS p y)
        (chosenContains B S hS p y) k) n := by
  let Ax := chosenBase B S hS p x
  let Ay := chosenBase B S hS p y
  let hx := chosenContains B S hS p x
  let hy := chosenContains B S hS p y
  let cx : ∀ k, B.Contains (Ax.truncation k) := fun k ↦ truncationContains B S Ax hx k
  let cy : ∀ k, B.Contains (Ay.truncation k) := fun k ↦ truncationContains B S Ay hy k
  let fm := baseRingMap B S hS p f
  letI : IsLocalHom fm := baseRingMap_isLocal B S hS p f hf
  let q := localQuotientMap fm n
  refine Over.homMk (ObjectProperty.homMk
    (X := ⟨Ax.truncation n, cx n⟩) (Y := ⟨Ay.truncation n, cy n⟩)
    (Spec.map (CommRingCat.ofHom q))) ?_
  apply ObjectProperty.hom_ext
  change (Spec.map (CommRingCat.ofHom q) ≫
      adicThickeningι Ay.R (maximalIdeal Ay.R) n) ≫ Ay.toS =
    adicThickeningι Ax.R (maximalIdeal Ax.R) n ≫ Ax.toS
  have hq : q.comp (Ideal.Quotient.mk (maximalIdeal Ay.R ^ (n + 1))) =
      (Ideal.Quotient.mk (maximalIdeal Ax.R ^ (n + 1))).comp fm := by
    simpa [q] using localQuotientMap_comp_mk fm n
  have hqCat :
      CommRingCat.ofHom (q.comp (Ideal.Quotient.mk (maximalIdeal Ay.R ^ (n + 1)))) =
      CommRingCat.ofHom ((Ideal.Quotient.mk (maximalIdeal Ax.R ^ (n + 1))).comp fm) :=
    congrArg CommRingCat.ofHom hq
  have hspec : Spec.map (CommRingCat.ofHom q) ≫
      adicThickeningι Ay.R (maximalIdeal Ay.R) n =
    adicThickeningι Ax.R (maximalIdeal Ax.R) n ≫
      baseMap B S hS p f := by
    rw [← baseMap_eq_SpecMap B S hS p f]
    simp only [adicThickeningι]
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map hqCat
  calc
    (Spec.map (CommRingCat.ofHom q) ≫
        adicThickeningι Ay.R (maximalIdeal Ay.R) n) ≫ Ay.toS =
        (adicThickeningι Ax.R (maximalIdeal Ax.R) n ≫
          baseMap B S hS p f) ≫ Ay.toS := by rw [hspec]
    _ = adicThickeningι Ax.R (maximalIdeal Ax.R) n ≫ Ax.toS := by
      rw [Category.assoc, baseMap_toS]

/-- The induced map of thickenings is the spectrum of `localQuotientMap`. -/
public theorem restrictionBaseMap_toScheme
    {x y : CompleteLocalObjectsFull B S hS p} (f : x ⟶ y)
    (hf : IsLocalBaseMap B S hS p f) (n : ℕ)
    [IsLocalHom (baseRingMap B S hS p f)] :
    (BigFppfOver.toScheme B S hS).map
        (restrictionBaseMap B S hS p f hf n) =
      Spec.map (CommRingCat.ofHom
        (localQuotientMap (baseRingMap B S hS p f) n)) :=
  rfl

/-- The map from a thickening to the complete local base is the canonical one. -/
public theorem restrictionToBase_toScheme (A : FormalBase S)
    (hA : B.Contains (Spec (.of A.R))) (contains : ∀ n, B.Contains (A.truncation n))
    (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map
        (restrictionToBase B S hS A hA contains n) =
      adicThickeningι A.R (maximalIdeal A.R) n :=
  rfl

/-- The identity induces the identity of infinitesimal thickenings. -/
public theorem restrictionBaseMap_id (x : CompleteLocalObjectsFull B S hS p)
    (n : ℕ) :
    restrictionBaseMap B S hS p (𝟙 x)
      (by
        change baseMap B S hS p (𝟙 x) (closedPoint _) = _
        rw [baseMap_id]
        rfl) n = 𝟙 _ := by
  let hid : IsLocalBaseMap B S hS p (𝟙 x) := by
    show baseMap B S hS p (𝟙 x) (closedPoint _) = _
    rw [baseMap_id]
    rfl
  let : IsLocalHom (baseRingMap B S hS p (𝟙 x)) :=
    baseRingMap_isLocal B S hS p (𝟙 x) hid
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  show (BigFppfOver.toScheme B S hS).map
      (restrictionBaseMap B S hS p (𝟙 x) hid n) = _
  rw [restrictionBaseMap_toScheme]
  simp only [baseRingMap_id, localQuotientMap_id, CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- The induced maps of infinitesimal thickenings are compatible with composition. -/
public theorem restrictionBaseMap_comp
    {x y z : CompleteLocalObjectsFull B S hS p}
    (f : x ⟶ y) (g : y ⟶ z)
    (hf : IsLocalBaseMap B S hS p f) (hg : IsLocalBaseMap B S hS p g) (n : ℕ) :
    restrictionBaseMap B S hS p f hf n ≫ restrictionBaseMap B S hS p g hg n =
      restrictionBaseMap B S hS p (f ≫ g)
        (by
          change localBaseMaps B S hS p f at hf
          change localBaseMaps B S hS p g at hg
          exact (localBaseMaps B S hS p).comp_mem f g hf hg) n := by
  let hfg : IsLocalBaseMap B S hS p (f ≫ g) := by
    change localBaseMaps B S hS p f at hf
    change localBaseMaps B S hS p g at hg
    exact (localBaseMaps B S hS p).comp_mem f g hf hg
  let : IsLocalHom (baseRingMap B S hS p f) := baseRingMap_isLocal B S hS p f hf
  let : IsLocalHom (baseRingMap B S hS p g) := baseRingMap_isLocal B S hS p g hg
  let : IsLocalHom (baseRingMap B S hS p (f ≫ g)) :=
    baseRingMap_isLocal B S hS p (f ≫ g) hfg
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  change (BigFppfOver.toScheme B S hS).map
      (restrictionBaseMap B S hS p f hf n) ≫
      (BigFppfOver.toScheme B S hS).map
        (restrictionBaseMap B S hS p g hg n) =
      (BigFppfOver.toScheme B S hS).map
        (restrictionBaseMap B S hS p (f ≫ g)
          (by
            change localBaseMaps B S hS p f at hf
            change localBaseMaps B S hS p g at hg
            exact (localBaseMaps B S hS p).comp_mem f g hf hg) n)
  rw [restrictionBaseMap_toScheme, restrictionBaseMap_toScheme,
    restrictionBaseMap_toScheme]
  show Spec.map (CommRingCat.ofHom
      (localQuotientMap (baseRingMap B S hS p f) n)) ≫
      Spec.map (CommRingCat.ofHom
        (localQuotientMap (baseRingMap B S hS p g) n)) =
    Spec.map (CommRingCat.ofHom
      (localQuotientMap (baseRingMap B S hS p (f ≫ g)) n))
  rw [← Spec.map_comp]
  congr 1
  simp only [baseRingMap_comp, localQuotientMap_comp]
  rfl

/-- The induced maps of infinitesimal thickenings commute with the inclusions of
successive thickenings. -/
public theorem restrictionBaseMap_succ
    {x y : CompleteLocalObjectsFull B S hS p} (f : x ⟶ y)
    (hf : IsLocalBaseMap B S hS p f) (n : ℕ) :
    truncationOverSucc B S hS (chosenBase B S hS p x)
        (fun k => truncationContains B S (chosenBase B S hS p x)
          (chosenContains B S hS p x) k) n ≫
      restrictionBaseMap B S hS p f hf (n + 1) =
    restrictionBaseMap B S hS p f hf n ≫
      truncationOverSucc B S hS (chosenBase B S hS p y)
        (fun k => truncationContains B S (chosenBase B S hS p y)
          (chosenContains B S hS p y) k) n := by
  let Ax := chosenBase B S hS p x
  let Ay := chosenBase B S hS p y
  let fm := baseRingMap B S hS p f
  let : IsLocalHom fm := baseRingMap_isLocal B S hS p f hf
  let qSucc := localQuotientMap fm (n + 1)
  let q := localQuotientMap fm n
  let tx := Ideal.Quotient.factorPow (maximalIdeal Ax.R) (Nat.le_succ (n + 1))
  let ty := Ideal.Quotient.factorPow (maximalIdeal Ay.R) (Nat.le_succ (n + 1))
  have htx : tx.comp (Ideal.Quotient.mk (maximalIdeal Ax.R ^ (n + 2))) =
      Ideal.Quotient.mk (maximalIdeal Ax.R ^ (n + 1)) := by
    simp [tx, Ideal.Quotient.factorPow]
  have hty : ty.comp (Ideal.Quotient.mk (maximalIdeal Ay.R ^ (n + 2))) =
      Ideal.Quotient.mk (maximalIdeal Ay.R ^ (n + 1)) := by
    simp [ty, Ideal.Quotient.factorPow]
  have hring : tx.comp qSucc = q.comp ty := by
    apply Ideal.Quotient.ringHom_ext
    rw [RingHom.comp_assoc, localQuotientMap_comp_mk,
      ← RingHom.comp_assoc, htx, ← localQuotientMap_comp_mk fm n,
      ← hty, ← RingHom.comp_assoc]
  refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
  show Spec.map (CommRingCat.ofHom tx) ≫
      Spec.map (CommRingCat.ofHom qSucc) =
    Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom ty)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom hring)

/-- The induced map of thickenings is compatible with the maps to the complete local
bases and the given morphism of objects. -/
public theorem restrictionBaseMap_comm
    {x y : CompleteLocalObjectsFull B S hS p} (f : x ⟶ y)
    (hf : IsLocalBaseMap B S hS p f) (n : ℕ) :
    restrictionBaseMap B S hS p f hf n ≫
        restrictionToBase B S hS (chosenBase B S hS p y)
          (chosenContains B S hS p y)
          (fun k ↦ truncationContains B S (chosenBase B S hS p y)
            (chosenContains B S hS p y) k) n =
      restrictionToBase B S hS (chosenBase B S hS p x)
        (chosenContains B S hS p x)
        (fun k ↦ truncationContains B S (chosenBase B S hS p x)
          (chosenContains B S hS p x) k) n ≫
      (eqToHom (chosenBase_eq B S hS p x).symm ≫ p.map f.1 ≫
          eqToHom (chosenBase_eq B S hS p y)) := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  let Ax := chosenBase B S hS p x
  let Ay := chosenBase B S hS p y
  let fm := baseRingMap B S hS p f
  let : IsLocalHom fm := baseRingMap_isLocal B S hS p f hf
  show (BigFppfOver.toScheme B S hS).map
      (restrictionBaseMap B S hS p f hf n) ≫
      (BigFppfOver.toScheme B S hS).map
        (restrictionToBase B S hS (chosenBase B S hS p y)
          (chosenContains B S hS p y)
          (fun k ↦ truncationContains B S (chosenBase B S hS p y)
            (chosenContains B S hS p y) k) n) =
    (BigFppfOver.toScheme B S hS).map
      (restrictionToBase B S hS (chosenBase B S hS p x)
        (chosenContains B S hS p x)
        (fun k ↦ truncationContains B S (chosenBase B S hS p x)
          (chosenContains B S hS p x) k) n) ≫
      (BigFppfOver.toScheme B S hS).map
        (eqToHom (chosenBase_eq B S hS p x).symm ≫ p.map f.1 ≫
          eqToHom (chosenBase_eq B S hS p y))
  rw [restrictionBaseMap_toScheme, restrictionToBase_toScheme,
    restrictionToBase_toScheme]
  show Spec.map (CommRingCat.ofHom (localQuotientMap fm n)) ≫
      adicThickeningι Ay.R (maximalIdeal Ay.R) n =
    adicThickeningι Ax.R (maximalIdeal Ax.R) n ≫
      baseMap B S hS p f
  rw [← baseMap_eq_SpecMap B S hS p f]
  simp only [adicThickeningι]
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom
    (localQuotientMap_comp_mk fm n))

/-- The morphism of restrictions induced by a morphism of complete local objects,
together with its base and its compatibility with the cartesian maps. -/
public noncomputable def restrictionArrowData
    (hp : p.IsFiberedInGroupoids)
    {x y : CompleteLocalObjectsFull B S hS p} (f : x ⟶ y)
    (hf : IsLocalBaseMap B S hS p f) (n : ℕ) :
    {g : restrictionLevel B S hS p hp x n ⟶ restrictionLevel B S hS p hp y n //
      p.map g = eqToHom (restrictionLevel_eq B S hS p hp x n) ≫
          restrictionBaseMap B S hS p f hf n ≫
            eqToHom (restrictionLevel_eq B S hS p hp y n).symm ∧
        g ≫ restrictionMap B S hS p hp y n =
          restrictionMap B S hS p hp x n ≫ f.1} := by
  let q := restrictionBaseMap B S hS p f hf n
  let rx := restrictionMap B S hS p hp x n
  let ry := restrictionMap B S hS p hp y n
  let hx := restrictionLevel_eq B S hS p hp x n
  let hy := restrictionLevel_eq B S hS p hp y n
  let bx := chosenBase_eq B S hS p x
  let bY := chosenBase_eq B S hS p y
  let fb := eqToHom bx.symm ≫ p.map f.1 ≫ eqToHom bY
  let qbase := eqToHom hx ≫ q ≫ eqToHom hy.symm
  let fx := restrictionToBase B S hS (chosenBase B S hS p x)
    (chosenContains B S hS p x)
    (fun k ↦ truncationContains B S (chosenBase B S hS p x)
      (chosenContains B S hS p x) k) n
  let fy := restrictionToBase B S hS (chosenBase B S hS p y)
    (chosenContains B S hS p y)
    (fun k ↦ truncationContains B S (chosenBase B S hS p y)
      (chosenContains B S hS p y) k) n
  have hbase := restrictionBaseMap_comm B S hS p f hf n
  letI : p.IsFibered := Functor.IsFiberedInGroupoids.isFibered hp
  haveI : p.IsHomLift (restrictionToBase B S hS (chosenBase B S hS p x)
      (chosenContains B S hS p x)
      (fun k ↦ truncationContains B S (chosenBase B S hS p x)
        (chosenContains B S hS p x) k) n) rx := by
    change p.IsHomLift _ (Functor.IsPreFibered.pullbackMap bx _)
    infer_instance
  haveI : p.IsHomLift (restrictionToBase B S hS (chosenBase B S hS p y)
      (chosenContains B S hS p y)
      (fun k ↦ truncationContains B S (chosenBase B S hS p y)
        (chosenContains B S hS p y) k) n) ry := by
    change p.IsHomLift _ (Functor.IsPreFibered.pullbackMap bY _)
    infer_instance
  have hcomm : qbase ≫ p.map ry = p.map rx ≫ p.map f.1 := by
    calc
      qbase ≫ p.map ry = eqToHom hx ≫ q ≫ fy ≫ eqToHom bY.symm := by
        dsimp [qbase]
        rw [IsHomLift.fac' p fy ry]
        simp [Category.assoc]
      _ = eqToHom hx ≫ fx ≫ fb ≫ eqToHom bY.symm := by
        change q ≫ fy = fx ≫ fb at hbase
        simpa [Category.assoc] using
          congrArg (fun z ↦ eqToHom hx ≫ z ≫ eqToHom bY.symm) hbase
      _ = eqToHom hx ≫ fx ≫ eqToHom bx.symm ≫ p.map f.1 := by
        simp [fb, Category.assoc]
      _ = p.map rx ≫ p.map f.1 := by
        rw [IsHomLift.fac' p fx rx]
        simp [Category.assoc]
  have hex := (hp.unique_lift ry (rx ≫ f.1) qbase
    (by simpa only [Functor.map_comp] using hcomm)).exists
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2⟩

/-- Two morphisms of restrictions with the same base and the same compatibility with the
cartesian maps agree. -/
public theorem restrictionArrow_ext
    (hp : p.IsFiberedInGroupoids)
    {x y : CompleteLocalObjectsFull B S hS p} (f : x ⟶ y)
    (hf : IsLocalBaseMap B S hS p f) (n : ℕ)
    (g₁ g₂ : restrictionLevel B S hS p hp x n ⟶
      restrictionLevel B S hS p hp y n)
    (hbase₁ : p.map g₁ =
      eqToHom (restrictionLevel_eq B S hS p hp x n) ≫
        restrictionBaseMap B S hS p f hf n ≫
          eqToHom (restrictionLevel_eq B S hS p hp y n).symm)
    (hbase₂ : p.map g₂ =
      eqToHom (restrictionLevel_eq B S hS p hp x n) ≫
        restrictionBaseMap B S hS p f hf n ≫
          eqToHom (restrictionLevel_eq B S hS p hp y n).symm)
    (hcomp₁ : g₁ ≫ restrictionMap B S hS p hp y n =
      restrictionMap B S hS p hp x n ≫ f.1)
    (hcomp₂ : g₂ ≫ restrictionMap B S hS p hp y n =
      restrictionMap B S hS p hp x n ≫ f.1) : g₁ = g₂ := by
  have hcomm : (eqToHom (restrictionLevel_eq B S hS p hp x n) ≫
      restrictionBaseMap B S hS p f hf n ≫
        eqToHom (restrictionLevel_eq B S hS p hp y n).symm) ≫
      p.map (restrictionMap B S hS p hp y n) =
      p.map (restrictionMap B S hS p hp x n ≫ f.1) := by
    rw [← hbase₁, ← Functor.map_comp, hcomp₁]
  obtain ⟨_, _, huniq⟩ := hp.unique_lift _ _ _ hcomm
  exact (huniq g₁ ⟨hbase₁, hcomp₁⟩).trans (huniq g₂ ⟨hbase₂, hcomp₂⟩).symm

/-- The canonical functor taking an object over a complete local ring to its
compatible system of restrictions to the infinitesimal thickenings. -/
@[stacks 07X6]
public noncomputable def approximationFunctorData
    (hp : p.IsFiberedInGroupoids) :
    {G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p //
      IsApproximationFunctor B S hS p G} := by
  classical
  letI : p.IsFibered := Functor.IsFiberedInGroupoids.isFibered hp
  let G : CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p := {
    obj := fun x ↦
      { base := chosenBase B S hS p x.obj
        contains := fun n ↦ truncationContains B S (chosenBase B S hS p x.obj)
          (chosenContains B S hS p x.obj) n
        level := fun n ↦ restrictionLevel B S hS p hp x.obj n
        level_eq := restrictionLevel_eq B S hS p hp x.obj
        transition := restrictionTransition B S hS p hp x.obj
        transition_lift := fun n ↦
          (restrictionTransitionData B S hS p hp x.obj n).property.1 }
    map := fun {X Y} f ↦
      { app := fun n ↦ (restrictionArrowData B S hS p hp f.1 f.2 n).1
        naturality := fun n ↦ by
          let fx := f.1
          let Ax := chosenBase B S hS p X.obj
          let Ay := chosenBase B S hS p Y.obj
          let cx : ∀ k, B.Contains (Ax.truncation k) :=
            fun k ↦ truncationContains B S Ax (chosenContains B S hS p X.obj) k
          let cy : ∀ k, B.Contains (Ay.truncation k) :=
            fun k ↦ truncationContains B S Ay (chosenContains B S hS p Y.obj) k
          let tx := restrictionTransition B S hS p hp X.obj n
          let ty := restrictionTransition B S hS p hp Y.obj n
          let rx := restrictionMap B S hS p hp X.obj n
          let ry := restrictionMap B S hS p hp Y.obj n
          let rxNext := restrictionMap B S hS p hp X.obj (n + 1)
          let ryNext := restrictionMap B S hS p hp Y.obj (n + 1)
          let sx := truncationOverSucc B S hS Ax cx n
          let sy := truncationOverSucc B S hS Ay cy n
          let qNext := restrictionBaseMap B S hS p fx f.2 (n + 1)
          let qNow := restrictionBaseMap B S hS p fx f.2 n
          let appNow := (restrictionArrowData B S hS p hp fx f.2 n).1
          let appNext := (restrictionArrowData B S hS p hp fx f.2 (n + 1)).1
          let hx := restrictionLevel_eq B S hS p hp X.obj n
          let hxNext := restrictionLevel_eq B S hS p hp X.obj (n + 1)
          let hy := restrictionLevel_eq B S hS p hp Y.obj n
          let hyNext := restrictionLevel_eq B S hS p hp Y.obj (n + 1)
          let qLeft := eqToHom hx ≫ (sx ≫ qNext) ≫ eqToHom hyNext.symm
          let qRight := eqToHom hx ≫ (qNow ≫ sy) ≫ eqToHom hyNext.symm
          have hbaseSq : sx ≫ qNext = qNow ≫ sy := restrictionBaseMap_succ B S hS p fx f.2 n
          have htransX : p.map tx = eqToHom hx ≫ sx ≫ eqToHom hxNext.symm := by
            let : p.IsHomLift sx tx := by
              change p.IsHomLift _ (restrictionTransition B S hS p hp X.obj n)
              simpa [restrictionTransition] using
                (restrictionTransitionData B S hS p hp X.obj n).property.1
            exact IsHomLift.fac' p sx tx
          have htransY : p.map ty = eqToHom hy ≫ sy ≫ eqToHom hyNext.symm := by
            let : p.IsHomLift sy ty := by
              change p.IsHomLift _ (restrictionTransition B S hS p hp Y.obj n)
              simpa [restrictionTransition] using
                (restrictionTransitionData B S hS p hp Y.obj n).property.1
            exact IsHomLift.fac' p sy ty
          have happNow : p.map appNow = eqToHom hx ≫ qNow ≫ eqToHom hy.symm :=
            (restrictionArrowData B S hS p hp fx f.2 n).property.1
          have happNext : p.map appNext =
              eqToHom hxNext ≫ qNext ≫ eqToHom hyNext.symm :=
            (restrictionArrowData B S hS p hp fx f.2 (n + 1)).property.1
          have hbaseLeft : p.map (tx ≫ appNext) = qLeft := by
            dsimp [qLeft]
            rw [Functor.map_comp, htransX, happNext]
            simp [Category.assoc]
          have hbaseRight : p.map (appNow ≫ ty) = qRight := by
            dsimp [qRight]
            rw [Functor.map_comp, happNow, htransY]
            simp [Category.assoc]
          have hcompLeft : (tx ≫ appNext) ≫ ryNext = rx ≫ fx.1 := by
            rw [Category.assoc,
              (restrictionArrowData B S hS p hp fx f.2 (n + 1)).property.2,
              ← Category.assoc]
            simpa [tx, restrictionTransition] using
              congrArg (fun u ↦ u ≫ fx.1)
                (restrictionTransitionData B S hS p hp X.obj n).property.2
          have hcompRight : (appNow ≫ ty) ≫ ryNext = rx ≫ fx.1 := by
            rw [Category.assoc, show ty ≫ ryNext = ry by
              simpa [ty, restrictionTransition] using
                (restrictionTransitionData B S hS p hp Y.obj n).property.2]
            exact (restrictionArrowData B S hS p hp fx f.2 n).property.2
          have hcomm : qLeft ≫ p.map ryNext = p.map (rx ≫ fx.1) := by
            calc
              qLeft ≫ p.map ryNext = p.map (tx ≫ appNext) ≫ p.map ryNext := by
                rw [hbaseLeft]
              _ = p.map ((tx ≫ appNext) ≫ ryNext) := by
                rw [← Functor.map_comp]
              _ = p.map (rx ≫ fx.1) := by rw [hcompLeft]
          obtain ⟨t, ht, huniq⟩ := hp.unique_lift ryNext (rx ≫ fx.1) qLeft hcomm
          have hleft := huniq (tx ≫ appNext) ⟨hbaseLeft, hcompLeft⟩
          have hrightBase : p.map (appNow ≫ ty) = qLeft := by
            rw [hbaseRight]
            dsimp [qRight, qLeft]
            rw [hbaseSq]
          have hright := huniq (appNow ≫ ty) ⟨hrightBase, hcompRight⟩
          exact hleft.trans hright.symm }
    map_id := by
      intro x
      apply FormalObject.Hom.ext
      intro n
      let f : x.obj ⟶ x.obj := 𝟙 x.obj
      have hf : IsLocalBaseMap B S hS p f := by
        change baseMap B S hS p (𝟙 x.obj) (closedPoint _) = _
        rw [baseMap_id]
        rfl
      let d := restrictionArrowData B S hS p hp f hf n
      change d.1 = 𝟙 _
      apply (restrictionArrow_ext B S hS p hp f hf n
        (𝟙 (restrictionLevel B S hS p hp x.obj n)) d.1 ?_ d.property.1 ?_
        d.property.2).symm
      · rw [restrictionBaseMap_id]
        simp
      · simp [f]
    map_comp := by
      intro x y z f g
      apply FormalObject.Hom.ext
      intro n
      let a := (restrictionArrowData B S hS p hp f.1 f.2 n).1
      let b := (restrictionArrowData B S hS p hp g.1 g.2 n).1
      let d := restrictionArrowData B S hS p hp (f ≫ g).1 (f ≫ g).2 n
      have hbasea := (restrictionArrowData B S hS p hp f.1 f.2 n).property.1
      have hbaseb := (restrictionArrowData B S hS p hp g.1 g.2 n).property.1
      have hbase : p.map (a ≫ b) =
          eqToHom (restrictionLevel_eq B S hS p hp x.obj n) ≫
            restrictionBaseMap B S hS p (f ≫ g).1 (f ≫ g).2 n ≫
              eqToHom (restrictionLevel_eq B S hS p hp z.obj n).symm := by
        rw [Functor.map_comp, hbasea, hbaseb]
        simpa [Category.assoc] using congrArg
          (fun q ↦ eqToHom (restrictionLevel_eq B S hS p hp x.obj n) ≫ q ≫
            eqToHom (restrictionLevel_eq B S hS p hp z.obj n).symm)
          (restrictionBaseMap_comp B S hS p f.1 g.1 f.2 g.2 n)
      have hcomp : (a ≫ b) ≫ restrictionMap B S hS p hp z.obj n =
          restrictionMap B S hS p hp x.obj n ≫ f.1.1 ≫ g.1.1 := by
        rw [Category.assoc,
          (restrictionArrowData B S hS p hp g.1 g.2 n).property.2,
          ← Category.assoc,
          (restrictionArrowData B S hS p hp f.1 f.2 n).property.2]
        simp only [Category.assoc]
      change d.1 = a ≫ b
      exact (restrictionArrow_ext B S hS p hp (f ≫ g).1 (f ≫ g).2 n
        (a ≫ b) d.1 hbase d.property.1 hcomp d.property.2).symm
  }
  refine ⟨G, ?_⟩
  refine ⟨fun x n ↦ ?_, ?_⟩
  · change restrictionLevel B S hS p hp x.obj n ⟶ x.obj.1
    exact restrictionMap B S hS p hp x.obj n
  refine ⟨fun x ↦ by simp [G], ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x n
    dsimp only [id]
    let : CategoryTheory.Functor.IsStronglyCartesian p
        (p.map (restrictionMap B S hS p hp x.obj n))
        (restrictionMap B S hS p hp x.obj n) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian hp
        (restrictionMap B S hS p hp x.obj n)
    infer_instance
  · intro x n
    simpa [G, restrictionTransition] using
      (restrictionTransitionData B S hS p hp x.obj n).property.2
  · intro x y f n
    simpa [G] using (restrictionArrowData B S hS p hp f.1 f.2 n).property.2
  · intro x n
    change (BigFppfOver.toScheme B S hS).map
        (eqToHom ((G.obj x).level_eq n).symm ≫
          p.map (restrictionMap B S hS p hp x.obj n) ≫
            eqToHom (chosenBase_eq B S hS p x.obj)) = _
    let A := chosenBase B S hS p x.obj
    let ha := chosenContains B S hS p x.obj
    let contains : ∀ k, B.Contains (A.truncation k) :=
      fun k ↦ truncationContains B S A ha k
    let : p.IsFibered := Functor.IsFiberedInGroupoids.isFibered hp
    have : p.IsHomLift
        (restrictionToBase B S hS A ha contains n)
        (restrictionMap B S hS p hp x.obj n) := by
      change p.IsHomLift _ (Functor.IsPreFibered.pullbackMap
        (chosenBase_eq B S hS p x.obj) _)
      infer_instance
    have hfac := IsHomLift.fac' p
      (restrictionToBase B S hS A ha contains n)
      (restrictionMap B S hS p hp x.obj n)
    rw [hfac]
    simpa [G] using restrictionToBase_toScheme B S hS A ha contains n

/-- The functor underlying the canonical complete-local-to-formal construction. -/
public noncomputable abbrev approximationFunctor (hp : p.IsFiberedInGroupoids) :
    CompleteLocalObjects B S hS p ⥤ FormalObject B S hS p :=
  (approximationFunctorData B S hS p hp).1

end

/-! ### Effective formal objects -/

section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace FormalObject

/-- A formal object is effective if it comes, up to isomorphism, from an
object over its complete local base by approximation. -/
@[stacks 07X7]
public abbrev IsEffective (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F : Type v} [Category.{w} F]
    (p : F ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (ξ : FormalObject B S hS p) : Prop :=
  (approximationFunctor B S hS p hp).essImage ξ

end FormalObject

end

end Deformation.Artin
