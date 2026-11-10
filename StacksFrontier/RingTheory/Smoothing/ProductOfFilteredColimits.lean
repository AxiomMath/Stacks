module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import Mathlib.CategoryTheory.WithTerminal.Lemmas
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TotallySplit
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Products of filtered colimits of smooth algebras

If `Λᵢ` is a filtered colimit of smooth `Rᵢ`-algebras for `i = 1, 2`, then `Λ₁ × Λ₂` is a
filtered colimit of smooth `(R₁ × R₂)`-algebras (Lemma `07F3`). Writing `Λ₁ = colim_{i ∈ I} Aᵢ`
and `Λ₂ = colim_{j ∈ J} Bⱼ` over filtered categories `I` and `J`, one has
`Λ₁ × Λ₂ ≅ colim_{(i, j)} (Aᵢ × Bⱼ)` over the filtered category `I × J`, because binary products
commute with filtered colimits, and each `Aᵢ × Bⱼ` is a smooth `(R₁ × R₂)`-algebra.

## Main definitions

* `UnderSmooth`: an object of `Under R` whose structure map is smooth.
* `PT`: `Λ` is a filtered colimit of smooth `R`-algebras.
* `IsRegularAlgebra`: `R → Λ` is flat with geometrically regular Noetherian fibres.
* `prodObj`, `prodUnderFunctor`: the product of an `R₁`-algebra and an `R₂`-algebra as an
  `(R₁ × R₂)`-algebra, and its functoriality.

## Main results

* `Algebra.Smooth.prod`: the product of a smooth `R₁`-algebra and a smooth `R₂`-algebra is a
  smooth `(R₁ × R₂)`-algebra.
* `prodUnderFunctor_preservesFilteredColimit`: `prodUnderFunctor` preserves the colimit of a
  product of filtered diagrams.
* `pt_product`: a product of filtered colimits of smooth algebras is a filtered colimit of smooth
  algebras.

## Implementation notes

`R`-algebras are modelled as objects of the under-category `Under (CommRingCat.of R)`, and
filtered colimits through `CategoryTheory.IsFiltered` and `CategoryTheory.Limits.IsColimit`.
Mathlib has no predicate for regular ring maps, so `IsRegularAlgebra` encodes one directly.

## References

* [Stacks Project, Tag 07F3](https://stacks.math.columbia.edu/tag/07F3)
-/

open CategoryTheory CategoryTheory.Limits TensorProduct

/-- An object `X` of the under-category `Under (CommRingCat.of R)` (i.e. an
`R`-algebra together with its structure map) is *smooth over `R`* if, with the algebra
structure induced by its structure morphism, it is smooth in the sense of
`Algebra.Smooth` (finitely presented and formally smooth, Tags 00T2 / 00TA). -/
@[ega "IV 17.3.2", sga "1 II 1.1"]
def UnderSmooth (R : CommRingCat) (X : Under R) : Prop :=
  letI : Algebra R X.right := X.hom.hom.toAlgebra
  Algebra.Smooth R X.right

/-- **Property PT.** For a ring map `R → Λ`, PT holds if `Λ` is a filtered
colimit of smooth `R`-algebras: there is a (small) filtered index category `I`, a diagram
`F : I ⥤ Under (CommRingCat.of R)` of `R`-algebras with each `F.obj i` smooth over `R`,
and a colimit cocone whose apex is isomorphic, as an `R`-algebra, to `Λ`. -/
def PT (R : Type) [CommRing R] (Λ : Type) [CommRing Λ] [Algebra R Λ] : Prop :=
  ∃ (I : Type) (_ : SmallCategory I) (_ : IsFiltered I)
    (F : I ⥤ Under (CommRingCat.of R)) (c : Cocone F),
      (∀ i, UnderSmooth (CommRingCat.of R) (F.obj i)) ∧ Nonempty (IsColimit c) ∧
      Nonempty (c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R Λ)))

/-- **Regular ring map, as an algebra.** `R → Λ` is regular if it is flat and
its fibres are geometrically regular Noetherian rings: for every prime `p` of `R` and
every finite field extension `k'` of the residue field `κ(p)`, the base change
`k' ⊗_R Λ` is a Noetherian regular ring.  (Base change along `R → κ(p) → k'`.) -/
@[ega "0 19.0.2" "more general", ega "0 19.6.5", ega "IV 6.8.1" "(iv), special case"]
def IsRegularAlgebra (R : Type) [CommRing R] (Λ : Type) [CommRing Λ] [Algebra R Λ] : Prop :=
  Module.Flat R Λ ∧
    ∀ (p : Ideal R) [p.IsPrime]
      (k' : Type) [Field k'] [Algebra p.ResidueField k'] [Module.Finite p.ResidueField k'],
      letI : Algebra R k' :=
        ((algebraMap p.ResidueField k').comp (algebraMap R p.ResidueField)).toAlgebra
      IsNoetherianRing (k' ⊗[R] Λ) ∧ IsRegularRing (k' ⊗[R] Λ)

/-- **Object-level product.** Given an `R₁`-algebra object `X` (in `Under R₁`) and an
`R₂`-algebra object `Y` (in `Under R₂`), form the `(R₁ × R₂)`-algebra object whose carrier
is the product ring `X.right × Y.right` and whose structure map is the componentwise
`prodMap` of the two structure maps.  This realises `A_i × B_j` as an `(R₁×R₂)`-algebra. -/
noncomputable def prodObj (R₁ R₂ : CommRingCat)
    (X : Under R₁) (Y : Under R₂) : Under (CommRingCat.of (R₁ × R₂)) :=
  Under.mk (Y := CommRingCat.of (X.right × Y.right))
    (CommRingCat.ofHom (X.hom.hom.prodMap Y.hom.hom))

/-- **Product functor** `Under R₁ × Under R₂ ⥤ Under (R₁ × R₂)`, sending a pair of
algebra objects to their `prodObj` and a pair of algebra maps to the componentwise
`prodMap`. -/
noncomputable def prodUnderFunctor (R₁ R₂ : CommRingCat) :
    Under R₁ × Under R₂ ⥤ Under (CommRingCat.of (R₁ × R₂)) where
  obj XY := prodObj R₁ R₂ XY.1 XY.2
  map {XY XY'} fg :=
    Under.homMk (CommRingCat.ofHom (fg.1.right.hom.prodMap fg.2.right.hom)) (by
      -- structure-map naturality square; reduces componentwise to the Under
      -- commutativity squares `fg.i.w`.
      have h1 := fg.1.w
      have h2 := fg.2.w
      exact CommRingCat.hom_ext <| RingHom.ext fun ⟨a, b⟩ ↦
        Prod.ext (congrArg (fun (r : _ →+* _) => r a) (congrArg CommRingCat.Hom.hom h1))
          (congrArg (fun (r : _ →+* _) => r b) (congrArg CommRingCat.Hom.hom h2)))
  map_id := by
    -- `prodMap (𝟙) (𝟙) = 𝟙`; componentwise on `Prod`.
    intro X
    apply Under.UnderMorphism.ext
    ext ⟨a, b⟩
    rfl
  map_comp := by
    -- `prodMap (f ≫ f') (g ≫ g') = prodMap f g ≫ prodMap f' g'`; componentwise.
    intro X Y Z f g
    apply Under.UnderMorphism.ext
    ext ⟨a, b⟩
    rfl

/-- **Congruence of `prodObj` along isomorphisms** (functoriality of `prodUnderFunctor` on
isos). -/
noncomputable def prodObj_congr (R₁ R₂ : CommRingCat)
    {X X' : Under R₁} {Y Y' : Under R₂} (eX : X ≅ X') (eY : Y ≅ Y') :
    prodObj R₁ R₂ X Y ≅ prodObj R₁ R₂ X' Y' :=
  (prodUnderFunctor R₁ R₂).mapIso (X := (X, Y)) (Y := (X', Y')) (Iso.prod eX eY)

/-- **Universe transfer for smoothness.** Smoothness of an `R`-algebra `A` transfers to
any `R'`-algebra `A'` (possibly in a different universe) related to it by a ring iso
`eR : R' ≃+* R` on the base and a ring iso `eA : A' ≃+* A` on the carrier, provided the
two algebra structures are compatible (`algebraMap R' A' = eA.symm ∘ algebraMap R A ∘ eR`).
The base change goes through `R` being smooth over `R'` along the iso `eR` (it is even
isomorphic, as an `R'`-algebra, to `R'` itself), then `Algebra.Smooth.comp`, then the
carrier iso via `Algebra.Smooth.of_equiv`. -/
private theorem smooth_transfer.{v, w} (R A : Type v) (R' A' : Type w)
    [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R' A']
    (eR : R' ≃+* R) (eA : A' ≃+* A)
    (hcompat : ∀ r : R', algebraMap R' A' r = eA.symm (algebraMap R A (eR r)))
    (hsm : Algebra.Smooth R A) :
    Algebra.Smooth R' A' := by
  have : Algebra.Smooth R A := hsm
  let instR'A : Algebra R' A := ((algebraMap R A).comp eR.toRingHom).toAlgebra
  have hR'A : Algebra.Smooth R' A := by
    let : Algebra R' R := eR.toRingHom.toAlgebra
    have : IsScalarTower R' R A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hSR : Algebra.Smooth R' R := by
      have ee : R ≃ₐ[R'] R' :=
        { eR.symm with
          commutes' := fun s => by
            change eR.symm (algebraMap R' R s) = s
            exact eR.symm_apply_apply s }
      exact Algebra.Smooth.of_equiv (R := R') (A := R') (B := R) ee.symm
    exact Algebra.Smooth.comp R' R A
  have eAR' : A ≃ₐ[R'] A' :=
    { eA.symm with
      commutes' := fun r => by
        change eA.symm ((algebraMap R A) (eR r)) = algebraMap R' A' r
        rw [hcompat] }
  exact Algebra.Smooth.of_equiv (R := R') (A := A) (B := A') eAR'

/-- **`ULift` of a smooth algebra is smooth.** Lifting both base `R` and carrier `A` by
`ULift.{u₂}` into the common universe `Type (max u₁ u₂)` (with the algebra structure
transported along `ULift.ringEquiv`) preserves smoothness. A direct application of
`smooth_transfer` with `eR = eA = ULift.ringEquiv`. -/
private theorem smooth_ulift.{u₁, u₂} (R A : Type u₁) [CommRing R] [CommRing A] [Algebra R A]
    (h : Algebra.Smooth R A) :
    letI : Algebra (ULift.{u₂} R) (ULift.{u₂} A) :=
      (((ULift.ringEquiv (R := A)).symm.toRingHom.comp
        ((algebraMap R A).comp (ULift.ringEquiv (R := R)).toRingHom))).toAlgebra
    Algebra.Smooth (ULift.{u₂} R) (ULift.{u₂} A) := by
  let : Algebra (ULift.{u₂} R) (ULift.{u₂} A) :=
    (((ULift.ringEquiv (R := A)).symm.toRingHom.comp
      ((algebraMap R A).comp (ULift.ringEquiv (R := R)).toRingHom))).toAlgebra
  exact smooth_transfer R A (ULift.{u₂} R) (ULift.{u₂} A)
    (ULift.ringEquiv) (ULift.ringEquiv) (fun r => rfl) h

/-- The single-universe case of `Algebra.Smooth.prod`. -/
private theorem smooth_prod_aux.{u}
    (R₁ R₂ A B : Type u) [CommRing R₁] [CommRing R₂] [CommRing A] [CommRing B]
    [Algebra R₁ A] [Algebra R₂ B]
    (hA : Algebra.Smooth R₁ A) (hB : Algebra.Smooth R₂ B) :
    letI : Algebra (R₁ × R₂) (A × B) :=
      ((algebraMap R₁ A).prodMap (algebraMap R₂ B)).toAlgebra
    Algebra.Smooth (R₁ × R₂) (A × B) := by
  let : Algebra (R₁ × R₂) R₁ := (RingHom.fst R₁ R₂).toAlgebra
  let : Algebra (R₁ × R₂) R₂ := (RingHom.snd R₁ R₂).toAlgebra
  have hR₁ : Algebra.Smooth (R₁ × R₂) R₁ := inferInstance
  have hR₂ : Algebra.Smooth (R₁ × R₂) R₂ := inferInstance
  let : Algebra (R₁ × R₂) A := ((algebraMap R₁ A).comp (RingHom.fst R₁ R₂)).toAlgebra
  let : Algebra (R₁ × R₂) B := ((algebraMap R₂ B).comp (RingHom.snd R₁ R₂)).toAlgebra
  have : IsScalarTower (R₁ × R₂) R₁ A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower (R₁ × R₂) R₂ B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.Smooth R₁ A := hA
  have : Algebra.Smooth R₂ B := hB
  have hsA : Algebra.Smooth (R₁ × R₂) A := Algebra.Smooth.comp (R₁ × R₂) R₁ A
  have hsB : Algebra.Smooth (R₁ × R₂) B := Algebra.Smooth.comp (R₁ × R₂) R₂ B
  -- `Bool`-indexed family `cond b A B`
  let : ∀ b : Bool, CommRing (cond b A B) := fun b => by cases b <;> assumption
  let : ∀ b : Bool, Algebra (R₁ × R₂) (cond b A B) := fun b => by cases b <;> assumption
  have hsfam : ∀ b : Bool, Algebra.Smooth (R₁ × R₂) (cond b A B) :=
    fun b => by cases b <;> assumption
  have hPiFP : Algebra.FinitePresentation (R₁ × R₂) (∀ b : Bool, cond b A B) :=
    Algebra.FinitePresentation.pi _
  have hPiFS : Algebra.FormallySmooth (R₁ × R₂) (∀ b : Bool, cond b A B) :=
    (Algebra.FormallySmooth.pi_iff _).mpr (fun b => (hsfam b).1)
  -- `A × B ≃ₐ Π_{Bool} cond b A B` w.r.t. the ambient `prodMap` algebra structure on `A × B`
  let e : (A × B) ≃ₐ[R₁ × R₂] (∀ b : Bool, cond b A B) :=
    { toFun := fun p b => match b with | true => p.1 | false => p.2
      invFun := fun f => (f true, f false)
      left_inv := fun p => rfl
      right_inv := fun f => by funext b; cases b <;> rfl
      map_mul' := fun p q => by funext b; cases b <;> rfl
      map_add' := fun p q => by funext b; cases b <;> rfl
      commutes' := fun r => by funext b; cases b <;> rfl }
  exact ⟨Algebra.FormallySmooth.of_equiv e.symm, Algebra.FinitePresentation.equiv e.symm⟩

/-- **The componentwise product of a smooth `R₁`-algebra and a smooth `R₂`-algebra is a smooth
`(R₁ × R₂)`-algebra.** The two factors may live in different universes: everything is `ULift`ed
into `Type (max u₁ u₂)`, where the single-universe `smooth_prod_aux` applies, and the result is
transferred back along the componentwise `ULift.ringEquiv` isomorphisms.

The relative dimension of such a product is *not* the dimension of each of its fibres: the two
factors may have different relative dimensions, so a product is the witness showing that a
smooth algebra with geometrically irreducible fibres can have fibres of unequal dimension. -/
public theorem Algebra.Smooth.prod.{u₁, u₂}
    (R₁ A : Type u₁) (R₂ B : Type u₂)
    [CommRing R₁] [CommRing A] [CommRing R₂] [CommRing B]
    [Algebra R₁ A] [Algebra R₂ B]
    (hA : Algebra.Smooth R₁ A) (hB : Algebra.Smooth R₂ B) :
    letI : Algebra (R₁ × R₂) (A × B) :=
      ((algebraMap R₁ A).prodMap (algebraMap R₂ B)).toAlgebra
    Algebra.Smooth (R₁ × R₂) (A × B) := by
  let : Algebra (R₁ × R₂) (A × B) :=
    ((algebraMap R₁ A).prodMap (algebraMap R₂ B)).toAlgebra
  -- `ULift` each factor into `Type (max u₁ u₂)`.
  let : Algebra (ULift.{u₂} R₁) (ULift.{u₂} A) :=
    (((ULift.ringEquiv (R := A)).symm.toRingHom.comp
      ((algebraMap R₁ A).comp (ULift.ringEquiv (R := R₁)).toRingHom))).toAlgebra
  let : Algebra (ULift.{u₁} R₂) (ULift.{u₁} B) :=
    (((ULift.ringEquiv (R := B)).symm.toRingHom.comp
      ((algebraMap R₂ B).comp (ULift.ringEquiv (R := R₂)).toRingHom))).toAlgebra
  have hA' : Algebra.Smooth (ULift.{u₂} R₁) (ULift.{u₂} A) := smooth_ulift R₁ A hA
  have hB' : Algebra.Smooth (ULift.{u₁} R₂) (ULift.{u₁} B) := smooth_ulift R₂ B hB
  -- product at the single universe `max u₁ u₂`.
  let : Algebra (ULift.{u₂} R₁ × ULift.{u₁} R₂) (ULift.{u₂} A × ULift.{u₁} B) :=
    ((algebraMap (ULift.{u₂} R₁) (ULift.{u₂} A)).prodMap
      (algebraMap (ULift.{u₁} R₂) (ULift.{u₁} B))).toAlgebra
  have hprod : Algebra.Smooth (ULift.{u₂} R₁ × ULift.{u₁} R₂) (ULift.{u₂} A × ULift.{u₁} B) :=
    smooth_prod_aux (ULift.{u₂} R₁) (ULift.{u₁} R₂) (ULift.{u₂} A) (ULift.{u₁} B) hA' hB'
  -- transfer back along the componentwise `ULift.ringEquiv`.
  refine smooth_transfer (ULift.{u₂} R₁ × ULift.{u₁} R₂) (ULift.{u₂} A × ULift.{u₁} B)
    (R₁ × R₂) (A × B)
    (RingEquiv.prodCongr (ULift.ringEquiv (R := R₁)).symm (ULift.ringEquiv (R := R₂)).symm)
    (RingEquiv.prodCongr (ULift.ringEquiv (R := A)).symm (ULift.ringEquiv (R := B)).symm)
    ?_ hprod
  rintro ⟨r1, r2⟩
  apply Prod.ext <;> rfl

/-- The product `X.right × Y.right` of a smooth `R₁`-algebra `X` and a smooth `R₂`-algebra
`Y` is a smooth `(R₁ × R₂)`-algebra. -/
lemma underSmooth_prodObj (R₁ R₂ : CommRingCat)
    (X : Under R₁) (Y : Under R₂)
    (hX : UnderSmooth R₁ X) (hY : UnderSmooth R₂ Y) :
    UnderSmooth (CommRingCat.of (R₁ × R₂)) (prodObj R₁ R₂ X Y) := by
  let : Algebra R₁ X.right := X.hom.hom.toAlgebra
  let : Algebra R₂ Y.right := Y.hom.hom.toAlgebra
  exact Algebra.Smooth.prod R₁ X.right R₂ Y.right hX hY

/-- The `prodObj` of two `Under.mk` of algebra maps is isomorphic, as an `(R₁ × R₂)`-algebra
object, to the `Under.mk` of the product algebra map
`(algebraMap R₁ Λ₁).prodMap (algebraMap R₂ Λ₂)`, that is, to the structure map placed on
`Λ₁ × Λ₂` over `R₁ × R₂`. The two objects are definitionally equal. -/
noncomputable def prodObj_mk_iso (R₁ R₂ Λ₁ Λ₂ : Type)
    [CommRing R₁] [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂]
    [Algebra R₁ Λ₁] [Algebra R₂ Λ₂] :
    prodObj (CommRingCat.of R₁) (CommRingCat.of R₂)
        (Under.mk (CommRingCat.ofHom (algebraMap R₁ Λ₁)))
        (Under.mk (CommRingCat.ofHom (algebraMap R₂ Λ₂)))
      ≅ Under.mk (CommRingCat.ofHom ((algebraMap R₁ Λ₁).prodMap (algebraMap R₂ Λ₂))) :=
  Iso.refl _

/-- **Product cocone** in `Under R₁ × Under R₂`: apex `(c₁.pt, c₂.pt)`, legs the pair of
the two colimit legs. -/
noncomputable def prodCocone {R₁ R₂ : CommRingCat}
    {I J : Type} [SmallCategory I] [SmallCategory J]
    {F : I ⥤ Under R₁} {G : J ⥤ Under R₂}
    (c₁ : Cocone F) (c₂ : Cocone G) : Cocone (F.prod G) :=
  { pt := (c₁.pt, c₂.pt)
    ι := { app := fun ij => (c₁.ι.app ij.1, c₂.ι.app ij.2)
           naturality := by
             rintro ⟨iX, jX⟩ ⟨iY, jY⟩ ⟨f, g⟩
             apply Prod.ext
             · simp
             · simp } }

/-- For filtered `I` and `J`, the product cocone of two colimit cocones `c₁` of `F` and `c₂` of
`G` is a colimit cocone of `F.prod G`. -/
noncomputable def prodCocone_isColimit {R₁ R₂ : CommRingCat}
    {I J : Type} [SmallCategory I] [SmallCategory J] [IsFiltered I] [IsFiltered J]
    {F : I ⥤ Under R₁} {G : J ⥤ Under R₂}
    (c₁ : Cocone F) (c₂ : Cocone G) (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    IsColimit (prodCocone c₁ c₂) := by
  have i1 : (CategoryTheory.Prod.fst I J).Final := by infer_instance
  have i2 : (CategoryTheory.Prod.snd I J).Final := by infer_instance
  have hd₁ : IsColimit (c₁.whisker (CategoryTheory.Prod.fst I J)) :=
    (Functor.Final.isColimitWhiskerEquiv (CategoryTheory.Prod.fst I J) c₁).symm hc₁
  have hd₂ : IsColimit (c₂.whisker (CategoryTheory.Prod.snd I J)) :=
    (Functor.Final.isColimitWhiskerEquiv (CategoryTheory.Prod.snd I J) c₂).symm hc₂
  exact
  { desc := fun s => (hd₁.desc ((CategoryTheory.Prod.fst _ _).mapCocone s),
                      hd₂.desc ((CategoryTheory.Prod.snd _ _).mapCocone s))
    fac := fun s ij => Prod.ext (hd₁.fac ((CategoryTheory.Prod.fst _ _).mapCocone s) ij)
      (hd₂.fac ((CategoryTheory.Prod.snd _ _).mapCocone s) ij)
    uniq := fun s m hm => Prod.ext
      (hd₁.uniq ((CategoryTheory.Prod.fst _ _).mapCocone s) m.1 fun ij =>
        congrArg Prod.fst (hm ij))
      (hd₂.uniq ((CategoryTheory.Prod.snd _ _).mapCocone s) m.2 fun ij =>
        congrArg Prod.snd (hm ij)) }

universe u

/-- The literal cartesian-product bifunctor on `Type` (carrier of `binaryProductFunctor`,
sending `(A, B) ↦ A × B`). -/
noncomputable def litProd.{w} : Type w × Type w ⥤ Type w :=
  Functor.uncurry.obj Types.binaryProductFunctor

namespace prodFilteredColimitAux

variable {K : Type} [SmallCategory K]
variable {C D : Type*} [Category C] [Category D] (P : K ⥤ C × D)

/-- First projection of a diagram into a product category. -/
noncomputable abbrev GP1 : K ⥤ C := P ⋙ CategoryTheory.Prod.fst _ _
/-- Second projection of a diagram into a product category. -/
noncomputable abbrev GP2 : K ⥤ D := P ⋙ CategoryTheory.Prod.snd _ _

/-- Componentwise cocone in a product category. -/
noncomputable def gprodCone (c1 : Cocone (GP1 P)) (c2 : Cocone (GP2 P)) : Cocone P where
  pt := (c1.pt, c2.pt)
  ι := { app := fun k => (c1.ι.app k, c2.ι.app k)
         naturality := by
           intro k k' f
           apply Prod.ext
           · simpa using c1.ι.naturality f
           · simpa using c2.ι.naturality f }

/-- A componentwise cocone is a colimit if both projections are. -/
noncomputable def gprodIsColimit (c1 : Cocone (GP1 P)) (c2 : Cocone (GP2 P))
    (h1 : IsColimit c1) (h2 : IsColimit c2) : IsColimit (gprodCone P c1 c2) where
  desc s := (h1.desc ((CategoryTheory.Prod.fst _ _).mapCocone s),
             h2.desc ((CategoryTheory.Prod.snd _ _).mapCocone s))
  fac s k := Prod.ext (h1.fac ((CategoryTheory.Prod.fst _ _).mapCocone s) k)
    (h2.fac ((CategoryTheory.Prod.snd _ _).mapCocone s) k)
  uniq s m hm := Prod.ext
    (h1.uniq ((CategoryTheory.Prod.fst _ _).mapCocone s) m.1 fun k => congrArg Prod.fst (hm k))
    (h2.uniq ((CategoryTheory.Prod.snd _ _).mapCocone s) m.2 fun k => congrArg Prod.snd (hm k))

variable {C' D' : Type*} [Category C'] [Category D']
variable [HasColimitsOfShape K C] [HasColimitsOfShape K D]

set_option backward.isDefEq.respectTransparency true in
/-- If `Φ` and `Ψ` preserve colimits of shape `K`, then `Φ.prod Ψ` sends the componentwise
colimit cocone of `P` to a colimit cocone. -/
noncomputable def prodMapIsColimit (Φ : C ⥤ C') (Ψ : D ⥤ D')
    [PreservesColimitsOfShape K Φ] [PreservesColimitsOfShape K Ψ] :
    IsColimit ((Φ.prod Ψ).mapCocone
      (gprodCone P (colimit.cocone (GP1 P)) (colimit.cocone (GP2 P)))) := by
  have e : (Φ.prod Ψ).mapCocone
      (gprodCone P (colimit.cocone (GP1 P)) (colimit.cocone (GP2 P)))
        = gprodCone (P ⋙ Φ.prod Ψ) (Φ.mapCocone (colimit.cocone (GP1 P)))
            (Ψ.mapCocone (colimit.cocone (GP2 P))) := rfl
  rw [e]
  exact gprodIsColimit _ _ _
    (isColimitOfPreserves Φ (colimit.isColimit _))
    (isColimitOfPreserves Ψ (colimit.isColimit _))

/-- `Functor.prod` preserves colimits of a shape that each factor preserves. -/
instance prod_preservesColimit (Φ : C ⥤ C') (Ψ : D ⥤ D')
    [PreservesColimitsOfShape K Φ] [PreservesColimitsOfShape K Ψ] :
    PreservesColimit P (Φ.prod Ψ) :=
  preservesColimit_of_preserves_colimit_cocone
    (gprodIsColimit P (colimit.cocone (GP1 P)) (colimit.cocone (GP2 P))
      (colimit.isColimit _) (colimit.isColimit _))
    (prodMapIsColimit P Φ Ψ)

end prodFilteredColimitAux

namespace prodFilteredColimitAux

variable {K : Type} [SmallCategory K] [IsFiltered K] (P : K ⥤ Type u × Type u)

/-- `litProd` (the cartesian product bifunctor on `Type`) acts componentwise on elements. -/
lemma litProd_map_apply {X Y : Type u × Type u} (f : X ⟶ Y) (p : (litProd.{u}).obj X) :
    (litProd.{u}).map f p = (f.1 p.1, f.2 p.2) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image under `litProd` of the componentwise colimit cocone of `P` is a colimit:
this is the `Type`-level statement that binary products commute with filtered colimits
(surjectivity is automatic; injectivity uses filteredness via `IsFiltered.bowtie`). -/
noncomputable def litProdMapIsColimit :
    IsColimit (litProd.mapCocone (gprodCone P (colimit.cocone (GP1 P)) (colimit.cocone (GP2
        P)))) := by
  set Q := P ⋙ litProd with hQ
  set t := litProd.mapCocone (gprodCone P (colimit.cocone (GP1 P)) (colimit.cocone (GP2 P))) with ht
  set m := (colimit.isColimit Q).desc t with hm
  have key : ∀ (k : K) (z : Q.obj k),
      m (colimit.ι Q k z) = (colimit.ι (GP1 P) k z.1, colimit.ι (GP2 P) k z.2) := by
    intro k z
    have h1 : m (colimit.ι Q k z) = t.ι.app k z := colimit.ι_desc_apply t k z
    rw [h1]
    change (litProd.map ((gprodCone P (colimit.cocone (GP1 P))
        (colimit.cocone (GP2 P))).ι.app k)) z = _
    rw [litProd_map_apply]
    rfl
  haveI : IsIso m := by
    rw [isIso_iff_bijective]
    refine ⟨fun u v huv ↦ ?_, ?_⟩
    · obtain ⟨k, a, rfl⟩ := Types.jointly_surjective' u
      obtain ⟨l, b, rfl⟩ := Types.jointly_surjective' v
      rw [key, key] at huv
      have h1 : colimit.ι (GP1 P) k a.1 = colimit.ι (GP1 P) l b.1 := congrArg Prod.fst huv
      have h2 : colimit.ι (GP2 P) k a.2 = colimit.ι (GP2 P) l b.2 := congrArg Prod.snd huv
      rw [Types.FilteredColimit.colimit_eq_iff] at h1 h2
      obtain ⟨m₁, f₁, g₁, e1⟩ := h1
      obtain ⟨m₂, f₂, g₂, e2⟩ := h2
      obtain ⟨s, α, β, hα, hβ⟩ := IsFiltered.bowtie f₁ f₂ g₁ g₂
      refine (Types.FilteredColimit.colimit_eq_iff Q).mpr ⟨s, f₁ ≫ α, g₁ ≫ α, ?_⟩
      apply Prod.ext
      · have hc1 : (GP1 P).map (f₁ ≫ α) a.1 = (GP1 P).map (g₁ ≫ α) b.1 := by
          simp only [Functor.map_comp, types_comp_apply]; rw [e1]
        change (litProd.map (P.map (f₁ ≫ α)) a).1 = (litProd.map (P.map (g₁ ≫ α)) b).1
        rw [litProd_map_apply, litProd_map_apply]
        exact hc1
      · have hc2 : (GP2 P).map (f₁ ≫ α) a.2 = (GP2 P).map (g₁ ≫ α) b.2 := by
          rw [hα, hβ]; simp only [Functor.map_comp, types_comp_apply]; rw [e2]
        change (litProd.map (P.map (f₁ ≫ α)) a).2 = (litProd.map (P.map (g₁ ≫ α)) b).2
        rw [litProd_map_apply, litProd_map_apply]
        exact hc2
    · rintro ⟨x, y⟩
      obtain ⟨k₁, a, rfl⟩ := Types.jointly_surjective' x
      obtain ⟨k₂, b, rfl⟩ := Types.jointly_surjective' y
      refine ⟨colimit.ι Q (IsFiltered.max k₁ k₂)
        ((GP1 P).map (IsFiltered.leftToMax k₁ k₂) a,
         (GP2 P).map (IsFiltered.rightToMax k₁ k₂) b), ?_⟩
      rw [key]
      apply Prod.ext
      · change colimit.ι (GP1 P) _ ((GP1 P).map (IsFiltered.leftToMax k₁ k₂) a) = _
        rw [← types_comp_apply ((GP1 P).map _) (colimit.ι (GP1 P) _), colimit.w]
      · change colimit.ι (GP2 P) _ ((GP2 P).map (IsFiltered.rightToMax k₁ k₂) b) = _
        rw [← types_comp_apply ((GP2 P).map _) (colimit.ι (GP2 P) _), colimit.w]
  exact IsColimit.ofPointIso (colimit.isColimit Q)

/-- `litProd` (the binary product on `Type`) preserves filtered colimits. -/
instance litProd_preservesColimit : PreservesColimit P litProd :=
  preservesColimit_of_preserves_colimit_cocone
    (gprodIsColimit P (colimit.cocone (GP1 P)) (colimit.cocone (GP2 P))
      (colimit.isColimit _) (colimit.isColimit _))
    (litProdMapIsColimit P)

end prodFilteredColimitAux

set_option backward.isDefEq.respectTransparency true in
/-- For filtered `I` and `J`, the underlying-set functor `(X, Y) ↦ X.right × Y.right` of
`prodUnderFunctor R₁ R₂` preserves the colimit of `F.prod G`: binary products commute with
filtered colimits in `Type`. -/
instance prodUnderForget_type_preservesColimit (R₁ R₂ : CommRingCat)
    {I J : Type} [SmallCategory I] [SmallCategory J] [IsFiltered I] [IsFiltered J]
    {F : I ⥤ Under R₁} {G : J ⥤ Under R₂} :
    PreservesColimit (F.prod G)
      ((prodUnderFunctor R₁ R₂ ⋙ Under.forget (CommRingCat.of (R₁ × R₂))) ⋙
        forget CommRingCat) := by
  have : IsFiltered (I × J) := inferInstance
  have hfg : PreservesColimitsOfShape (I × J) (forget CommRingCat) :=
    (preservesFilteredColimitsOfSize_shrink (forget CommRingCat)).preserves_filtered_colimits (I ×
        J)
  have hu1 : PreservesColimitsOfShape (I × J) (Under.forget R₁ ⋙ forget CommRingCat) :=
    inferInstance
  have hu2 : PreservesColimitsOfShape (I × J) (Under.forget R₂ ⋙ forget CommRingCat) :=
    inferInstance
  -- The underlying functor `(X, Y) ↦ X.right × Y.right` equals
  -- `((Under.forget R₁ ⋙ forget) × (Under.forget R₂ ⋙ forget)) ⋙ litProd` definitionally.
  have heq :
      ((prodUnderFunctor R₁ R₂ ⋙ Under.forget (CommRingCat.of (R₁ × R₂))) ⋙ forget CommRingCat)
        = (((Under.forget R₁ ⋙ forget CommRingCat).prod
            (Under.forget R₂ ⋙ forget CommRingCat)) ⋙ litProd) := rfl
  rw [heq]
  have : PreservesColimit (F.prod G)
      ((Under.forget R₁ ⋙ forget CommRingCat).prod (Under.forget R₂ ⋙ forget CommRingCat)) :=
    prodFilteredColimitAux.prod_preservesColimit (F.prod G) _ _
  exact comp_preservesColimit _ litProd

/-- For filtered `I` and `J`, `prodUnderFunctor R₁ R₂` preserves the colimit of `F.prod G`:
a product of filtered colimits of algebras is a filtered colimit. -/
instance prodUnderFunctor_preservesFilteredColimit (R₁ R₂ : CommRingCat)
    {I J : Type} [SmallCategory I] [SmallCategory J] [IsFiltered I] [IsFiltered J]
    {F : I ⥤ Under R₁} {G : J ⥤ Under R₂} :
    PreservesColimit (F.prod G) (prodUnderFunctor R₁ R₂) := by
  -- Reflect along `Under.forget` and `forget CommRingCat` to the `Type`-level statement
  -- `prodUnderForget_type_preservesColimit`.
  have : IsConnected (I × J) := IsFiltered.isConnected (I × J)
  have : IsFiltered (I × J) := inferInstance
  -- `forget CommRingCat` preserves the filtered colimit (universe-shrunk to the `Type 0`
  -- shape `I × J`).
  have hpc : PreservesColimit
      (F.prod G ⋙ prodUnderFunctor R₁ R₂ ⋙ Under.forget (CommRingCat.of (R₁ × R₂)))
      (forget CommRingCat) := by
    have : PreservesFilteredColimitsOfSize.{0,0} (forget CommRingCat) :=
      preservesFilteredColimitsOfSize_shrink _
    have : PreservesColimitsOfShape (I × J) (forget CommRingCat) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits (I × J)
    infer_instance
  -- `forget CommRingCat` reflects this colimit (it reflects isomorphisms and preserves it).
  have hrefl : ReflectsColimit
      (F.prod G ⋙ prodUnderFunctor R₁ R₂ ⋙ Under.forget (CommRingCat.of (R₁ × R₂)))
      (forget CommRingCat) := reflectsColimit_of_reflectsIsomorphisms _ _
  -- Binary products commute with filtered colimits in `Type`.
  have hstep3 : PreservesColimit (F.prod G)
      ((prodUnderFunctor R₁ R₂ ⋙ Under.forget (CommRingCat.of (R₁ × R₂))) ⋙ forget CommRingCat) :=
    prodUnderForget_type_preservesColimit R₁ R₂
  -- Reflect `Type`-preservation up to `CommRingCat`-preservation …
  have hstep2 : PreservesColimit (F.prod G)
      (prodUnderFunctor R₁ R₂ ⋙ Under.forget (CommRingCat.of (R₁ × R₂))) :=
    preservesColimit_of_reflects_of_preserves
      (prodUnderFunctor R₁ R₂ ⋙ Under.forget (CommRingCat.of (R₁ × R₂)))
      (forget CommRingCat)
  -- … and up to `Under (R₁×R₂)`-preservation.
  exact preservesColimit_of_reflects_of_preserves (prodUnderFunctor R₁ R₂)
    (Under.forget (CommRingCat.of (R₁ × R₂)))

/-- For filtered `I` and `J` and colimit cocones `c₁` of `F` and `c₂` of `G`, a colimit cocone
of `(F.prod G) ⋙ prodUnderFunctor R₁ R₂` together with an isomorphism of its apex with
`prodObj R₁ R₂ c₁.pt c₂.pt`. -/
noncomputable def prodUnderFunctor_isColimit (R₁ R₂ : CommRingCat)
    (I J : Type) [SmallCategory I] [SmallCategory J] [IsFiltered I] [IsFiltered J]
    (F : I ⥤ Under R₁) (G : J ⥤ Under R₂)
    (c₁ : Cocone F) (c₂ : Cocone G) (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    {d : Cocone ((F.prod G) ⋙ prodUnderFunctor R₁ R₂) //
      Nonempty (IsColimit d) ∧ Nonempty (d.pt ≅ prodObj R₁ R₂ c₁.pt c₂.pt)} :=
  -- The chosen cocone is `mapCocone` of the product cocone; its apex is
  -- `prodObj R₁ R₂ c₁.pt c₂.pt` definitionally.
  ⟨(prodUnderFunctor R₁ R₂).mapCocone (prodCocone c₁ c₂),
    ⟨isColimitOfPreserves (prodUnderFunctor R₁ R₂) (prodCocone_isColimit c₁ c₂ hc₁ hc₂)⟩,
    ⟨Iso.refl _⟩⟩

/-- Let `R_i → Λ_i` (`i = 1, 2`) be ring maps of Noetherian rings. If PT holds for `R_1 → Λ_1`
and for `R_2 → Λ_2`, then PT holds for the product ring map `R_1 × R_2 → Λ_1 × Λ_2` (with the
componentwise algebra structure). -/
@[stacks 07F3]
theorem pt_product
    (R₁ R₂ Λ₁ Λ₂ : Type)
    [CommRing R₁] [CommRing R₂] [CommRing Λ₁] [CommRing Λ₂]
    [Algebra R₁ Λ₁] [Algebra R₂ Λ₂]
    [IsNoetherianRing R₁] [IsNoetherianRing Λ₁]
    [IsNoetherianRing R₂] [IsNoetherianRing Λ₂]
    (hPT₁ : PT R₁ Λ₁) (hPT₂ : PT R₂ Λ₂) :
    letI : Algebra (R₁ × R₂) (Λ₁ × Λ₂) :=
      ((algebraMap R₁ Λ₁).prodMap (algebraMap R₂ Λ₂)).toAlgebra
    PT (R₁ × R₂) (Λ₁ × Λ₂) := by
  -- Decompose the two PT hypotheses into filtered diagrams + colimit cocones + apex isos.
  obtain ⟨I, instI, instFiltI, F, c₁, hsmooth₁, ⟨hcol₁⟩, ⟨hiso₁⟩⟩ := hPT₁
  obtain ⟨J, instJ, instFiltJ, G, c₂, hsmooth₂, ⟨hcol₂⟩, ⟨hiso₂⟩⟩ := hPT₂
  -- Index: the product `I × J` (filtered as a product of filtered categories).
  -- Diagram: `(F.prod G) ⋙ prodUnderFunctor`, i.e. `(i,j) ↦ (F.obj i).right × (G.obj j).right`.
  -- Colimit cocone and apex: from `prodUnderFunctor_isColimit`.
  obtain ⟨d, ⟨hd⟩, ⟨e⟩⟩ := prodUnderFunctor_isColimit (CommRingCat.of R₁) (CommRingCat.of R₂)
    I J F G c₁ c₂ hcol₁ hcol₂
  refine ⟨I × J, inferInstance, inferInstance,
    (F.prod G) ⋙ prodUnderFunctor (CommRingCat.of R₁) (CommRingCat.of R₂), d, ?_, ⟨hd⟩, ?_⟩
  · -- Each object `(F.obj i).right × (G.obj j).right` is smooth over `R₁ × R₂`.
    rintro ⟨i, j⟩
    exact underSmooth_prodObj _ _ _ _ (hsmooth₁ i) (hsmooth₂ j)
  · -- Apex isomorphism to `Under.mk (algebraMap (R₁×R₂) (Λ₁×Λ₂))`:
    -- apex ≅ prodObj _ c₁.pt c₂.pt
    --      ≅ prodObj _ (Under.mk …₁) (Under.mk …₂)  (`hiso₁`, `hiso₂` via `prodObj_congr`)
    --      ≅ Under.mk (prodMap …)                    (`prodObj_mk_iso`).
    exact ⟨e ≪≫ prodObj_congr _ _ hiso₁ hiso₂ ≪≫ prodObj_mk_iso R₁ R₂ Λ₁ Λ₂⟩
