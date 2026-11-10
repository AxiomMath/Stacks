module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeTFAEAssembly

/-!
# The source identification of the cube at a chart is bijective

`AlgebraicGeometry.BaseChangeChart.localRingsSourceMap` is the source identification of the cube
of localizations at a chart, on the generators `1 ⊗ m`. Transposed along
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V') → 𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}` it is a map

`(𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}) ⊗_{𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')}
    H^n(RΓ(U,K)|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V'))  ⟶
  H^n(K_{g'x'}|_{𝒪_{S,s}} ⊗ᴸ_{𝒪_{S,s}} 𝒪_{S',s'})`

and this module proves it bijective, which is what the final assembly of Stacks 0DJ8 consumes.

The transpose is bijective because the extension of scalars along
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V') → 𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}` splits into the two base
changes `- ⊗_{𝒪_{S'}(V')} 𝒪_{S',s'}` and `𝒪_{X,g'x'} ⊗_{𝒪_X(U)} -`, by
`Stacks.TensorProductPushout.mapLocalizedRearrange`, and the source identification is a composite
of the chart's two corner moves of the cube on cohomology with the germ comparison of the local
rings of `X`, each of which is an isomorphism. What has to be checked by hand is that the
composite *is* the transpose, which is done on the generators `b ⊗ (c · ζ)` of the source.

## Main results

* `ModuleCat.bijective_extendScalarsTranspose_of_rearrange`: the general reduction, for a pushout
  of localizations, of the bijectivity of a transpose to that of the two base changes it splits
  into.
* `AlgebraicGeometry.BaseChangeChart.exists_localRingsSourceComposite`: the composite, with its
  value on the generators.
* `AlgebraicGeometry.BaseChangeChart.bijective_extendScalarsTranspose_localRingsSourceMap`: the
  bijectivity itself.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open scoped TensorProduct ChangeOfRings

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

/-- **Two commuting squares with central endomorphisms compose.** If an endomorphism `ν` of the
source is carried to `κ` by `α` and `κ` to `μ` by `β`, then `ν` is carried to `μ` by `α ≫ β`.

Stated with every object and morphism a variable: the affine reduction of Stacks 0DJ8 needs it
at morphisms of derived categories whose descriptions are long enough that reassociating the
composite in place exhausts the elaborator's budget. -/
public theorem comp_comm_of_comm_comm {𝒞 : Type*} [Category 𝒞] {W X Y : 𝒞}
    (α : W ⟶ X) (β : X ⟶ Y) (ν : W ⟶ W) (κ : X ⟶ X) (μ : Y ⟶ Y)
    (h₁ : ν ≫ α = α ≫ κ) (h₂ : κ ≫ β = β ≫ μ) : ν ≫ α ≫ β = (α ≫ β) ≫ μ := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

end CategoryTheory

namespace ModuleCat

/-- **Two additive maps out of a tensor product agreeing on pure tensors agree.** Stated for
bare functions on the carrier of a tensor product of two objects of `ModuleCat A`, which is the
form in which the affine reduction of Stacks 0DJ8 needs it: the two maps compared there are a
transpose, which is a morphism, and a composite of rearrangements and of isomorphisms over
intermediate rings, which is only a bijection of additive groups. -/
public theorem fun_eq_of_tmul {A : Type u} [CommRing A] (E M : ModuleCat.{u} A) {N : Type u}
    [AddCommGroup N] (F T : (E ⊗[A] M : Type u) → N)
    (hF : ∀ z z', F (z + z') = F z + F z')
    (hT : ∀ z z', T (z + z') = T z + T z')
    (h : ∀ (x : E) (m : M), F (x ⊗ₜ[A] m) = T (x ⊗ₜ[A] m)) (z : E ⊗[A] M) : F z = T z := by
  induction z using TensorProduct.inductionOn with
  | tmul x m => exact h x m
  | add z z' hz hz' => rw [hF, hT, hz, hz']

/-- **A transpose is the unique additive map with the right values on the pure tensors.** An
additive map sending `x ⊗ m` to `x • v m` agrees with the transpose of `v` everywhere.

A bare function is taken rather than a morphism: the consumer's candidate is a composite of
rearrangements of tensor products and of isomorphisms over intermediate rings, which is a
bijection and additive long before it is known to be linear over the target ring. -/
public theorem extendScalarsTranspose_hom_eq {A A₂ : Type u} [CommRing A] [CommRing A₂]
    (g : A →+* A₂) {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₂}
    (v : M ⟶ (ModuleCat.restrictScalars.{u} g).obj N)
    (T : (ModuleCat.extendScalars.{u, u, u} g).obj M → N)
    (hadd : ∀ z z', T (z + z') = T z + T z')
    (hT : ∀ (x : A₂) (m : M),
      T (show (ModuleCat.extendScalars.{u, u, u} g).obj M from x ⊗ₜ[A,g] m) =
        x • (show N from v.hom m)) (z : (ModuleCat.extendScalars.{u, u, u} g).obj M) :
    (extendScalarsTranspose g v).hom z = T z := by
  exact fun_eq_of_tmul ((ModuleCat.restrictScalars.{u} g).obj (ModuleCat.of A₂ A₂)) M
    (extendScalarsTranspose g v).hom T (fun z z' => map_add _ z z') hadd
    (fun x m => ((congrArg (extendScalarsTranspose g v).hom
      (extendScalars_tmul_eq_smul_one_tmul g M x m)).trans
        (extendScalarsTranspose_smul_one_tmul g v x m)).trans (hT x m).symm) z

/-- **A transpose is bijective as soon as some additive bijection has its values on the pure
tensors.** -/
public theorem bijective_extendScalarsTranspose {A A₂ : Type u} [CommRing A] [CommRing A₂]
    (g : A →+* A₂) {M : ModuleCat.{u} A} {N : ModuleCat.{u} A₂}
    (v : M ⟶ (ModuleCat.restrictScalars.{u} g).obj N)
    (T : (ModuleCat.extendScalars.{u, u, u} g).obj M → N)
    (hadd : ∀ z z', T (z + z') = T z + T z')
    (hT : ∀ (x : A₂) (m : M),
      T (show (ModuleCat.extendScalars.{u, u, u} g).obj M from x ⊗ₜ[A,g] m) =
        x • (show N from v.hom m))
    (hbij : Function.Bijective T) :
    Function.Bijective (extendScalarsTranspose g v).hom :=
  Eq.mpr (congrArg Function.Bijective
    (funext fun z => extendScalarsTranspose_hom_eq g v T hadd hT z)) hbij

/-- **A transpose along a map into a tensor product of rings is bijective as soon as some
additive bijection has its values on the generators `(b ⊗ c) ⊗ m`.** The pure tensors of
`E ⊗_D F` generate it additively, so the values on those generators determine the transpose. -/
public theorem bijective_extendScalarsTranspose_tmul {A D E F : Type u} [CommRing A]
    [CommRing D] [CommRing E] [CommRing F] [Algebra D E] [Algebra D F]
    (g : A →+* E ⊗[D] F) {M : ModuleCat.{u} A} {N : ModuleCat.{u} (E ⊗[D] F)}
    (v : M ⟶ (ModuleCat.restrictScalars.{u} g).obj N)
    (T : (ModuleCat.extendScalars.{u, u, u} g).obj M → N)
    (hadd : ∀ z z', T (z + z') = T z + T z')
    (hT : ∀ (b : E) (c : F) (m : M),
      T (show (ModuleCat.extendScalars.{u, u, u} g).obj M from (b ⊗ₜ[D] c) ⊗ₜ[A,g] m) =
        (b ⊗ₜ[D] c : E ⊗[D] F) • (show N from v.hom m))
    (hbij : Function.Bijective T) :
    Function.Bijective (extendScalarsTranspose g v).hom := by
  refine bijective_extendScalarsTranspose g v T hadd (fun x m => ?_) hbij
  induction x using TensorProduct.inductionOn with
  | tmul b c => exact hT b c m
  | add x x' hx hx' =>
      exact (congrArg T (TensorProduct.add_tmul (R := A)
          (M := ((ModuleCat.restrictScalars.{u} g).obj
            (ModuleCat.of (E ⊗[D] F) (E ⊗[D] F)) : Type u)) x x' m)).trans
        ((hadd _ _).trans ((congrArg₂ (· + ·) hx hx').trans (add_smul x x' _).symm))

/-- **A transpose along a pushout of localizations is bijective once the two base changes it
splits into are.** Let `R → A` and `R → R'` be commutative rings, `R_S` a localization of `R`,
and `B`, `C` algebras over `R_S` compatibly with their `A`-, resp. `R'`-algebra structures. For
`M` an `A ⊗_R R'`-module and `N` a `B ⊗_{R_S} C`-module, a map `v : M ⟶ N` over
`A ⊗_R R' → B ⊗_{R_S} C` transposes to `(B ⊗_{R_S} C) ⊗_{A ⊗_R R'} M ⟶ N`; the source is
`B ⊗_A (M ⊗_{R'} C)` by `Stacks.TensorProductPushout.localizedRearrange`, so an identification
`e` of `M ⊗_{R'} C` with an `A`-module `G` and a bijection `Ξ` of `B ⊗_A G` with `N` computing
`v` on the pure tensors make the transpose bijective.

This is the shape in which the affine reduction of Stacks 0DJ8 needs it: there `Ξ` is the
composite of the germ comparison of the local rings of `X` with the two corner moves of the cube
on cohomology, and `hΞ` is the statement that that composite is the source identification of the
cube, which is what has to be checked by hand. -/
public theorem bijective_extendScalarsTranspose_of_rearrange
    {R A R' Rp B C : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing Rp]
    [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R R'] [Algebra R Rp]
    [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Algebra Rp B] [IsScalarTower R Rp B]
    [Algebra R' C] [Algebra R C] [IsScalarTower R R' C] [Algebra Rp C] [IsScalarTower R Rp C]
    (S : Submonoid R) [IsLocalization S Rp]
    {M : ModuleCat.{u} (A ⊗[R] R')} [Module A (M : Type u)] [Module R' (M : Type u)]
    [instA : IsScalarTower A (A ⊗[R] R') (M : Type u)]
    [instR' : IsScalarTower R' (A ⊗[R] R') (M : Type u)]
    [instCC : SMulCommClass R' A (M : Type u)]
    {G : Type u} [AddCommGroup G] [Module A G] (e : ((M : Type u) ⊗[R'] C) ≃+ G)
    (he : ∀ (a : A) (m : (M : Type u)) (c : C), e ((a • m) ⊗ₜ[R'] c) = a • e (m ⊗ₜ[R'] c)) :
    letI := Stacks.TensorProductPushout.mapAlgebraMid (R := R) (A := A) (R' := R') (Rp := Rp)
      (B := B) (C := C)
    ∀ {N : ModuleCat.{u} (B ⊗[Rp] C)}
      (v : M ⟶ (ModuleCat.restrictScalars.{u} (algebraMap (A ⊗[R] R') (B ⊗[Rp] C))).obj N)
      (Ξ : (B ⊗[A] G) → (N : Type u)),
      (∀ z z', Ξ (z + z') = Ξ z + Ξ z') → Function.Bijective Ξ →
      (∀ (b : B) (c : C) (m : (M : Type u)),
        Ξ (b ⊗ₜ[A] e (m ⊗ₜ[R'] c)) =
          (b ⊗ₜ[Rp] c : B ⊗[Rp] C) • (show (N : Type u) from v.hom m)) →
      Function.Bijective (ModuleCat.extendScalarsTranspose
        (algebraMap (A ⊗[R] R') (B ⊗[Rp] C)) v).hom := by
  let := Stacks.TensorProductPushout.mapAlgebraMid (R := R) (A := A) (R' := R') (Rp := Rp)
    (B := B) (C := C)
  intro N v Ξ hadd hbij hΞ
  have hlin : ∀ (a : A) (x : (M : Type u) ⊗[R'] C), e (a • x) = a • e x := by
    intro a x
    induction x using TensorProduct.inductionOn with
    | tmul m c => rw [TensorProduct.smul_tmul', he]
    | add x x' hx hx' => rw [smul_add, map_add, map_add, hx, hx', smul_add]
  let Φ : ((B ⊗[Rp] C) ⊗[A ⊗[R] R'] (M : Type u)) ≃+ B ⊗[A] G :=
    (Stacks.TensorProductPushout.mapLocalizedRearrange S (M := (M : Type u))).trans
      (TensorProduct.congr (LinearEquiv.refl A B) (AddEquiv.toLinearEquiv e hlin)).toAddEquiv
  refine bijective_extendScalarsTranspose_tmul _ v (fun z => Ξ (Φ z))
    (fun z z' => (congrArg Ξ (map_add Φ z z')).trans (hadd _ _)) (fun b c m => ?_)
    (hbij.comp Φ.bijective)
  refine Eq.trans (congrArg Ξ ?_) (hΞ b c m)
  exact congrArg (TensorProduct.congr (LinearEquiv.refl A B) (AddEquiv.toLinearEquiv e hlin))
    (Stacks.TensorProductPushout.mapLocalizedRearrange_tmul S (M := (M : Type u)) b c m)

end ModuleCat

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The germ identification of the derived sections of a chart is equivariant for the local
ring of `X`.** Multiplication by `b : 𝒪_{X, g' x'}` on the derived stalk of `K` corresponds, on
`RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{Spec 𝒪_X(U), q}` read over `𝒪_X(U)`, to multiplication by the image of
`b` under the chart's comparison of the two local rings; and
`AlgebraicGeometry.BaseChangeChart.restrictGermDerivedStalkSectionsIso` carries the one to the
other.

The two scalars act on complexes over *different* rings, so neither side is the restriction of
scalars of the other: the identification is a composite of the germ comparison of the derived
sections with a coherence isomorphism of two restrictions of scalars, and what makes the square
commute is that `x • 𝟙` is central together with
`RingTheory.TorIndependence.mapDerivedCategory_restrictScalars_smul`. -/
public theorem restrictGermDerivedStalkSectionsIso_smul_comm
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (b : ToType (X.presheaf.stalk (g' (ch.incU' y)))) :
    (ModuleCat.restrictScalars.{u}
            (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.map
          ((ch.stalkCompAIso y).hom.hom b • 𝟙 ((totalDerivedExtensionScalars.{u, u, u}
            (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
            ((affineDerivedSections ch.incU).obj K))) ≫
        (ch.restrictGermDerivedStalkSectionsIso y K hK).hom =
      (ch.restrictGermDerivedStalkSectionsIso y K hK).hom ≫
        (ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.map
          (b • 𝟙 ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) := by
  have hcentral : ((ch.stalkCompAIso y).hom.hom b • 𝟙 ((totalDerivedExtensionScalars.{u, u, u}
          (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
          ((affineDerivedSections ch.incU).obj K))) ≫
        (ch.germDerivedStalkSectionsIso y K hK).hom =
      (ch.germDerivedStalkSectionsIso y K hK).hom ≫
        ((ch.stalkCompAIso y).hom.hom b • 𝟙
          ((ModuleCat.restrictScalars.{u, u, u}
              (ch.stalkCompAIso y).inv.hom).mapDerivedCategory.obj
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K))) := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have hQ : (ModuleCat.restrictScalars.{u, u, u}
        (ch.stalkCompAIso y).inv.hom).mapDerivedCategory.map
          (b • 𝟙 ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) =
      (ch.stalkCompAIso y).hom.hom b • 𝟙
        ((ModuleCat.restrictScalars.{u, u, u}
            (ch.stalkCompAIso y).inv.hom).mapDerivedCategory.obj
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) := by
    have h := RingTheory.TorIndependence.mapDerivedCategory_restrictScalars_smul
      (ch.stalkCompAIso y).inv.hom ((ch.stalkCompAIso y).hom.hom b)
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)
    rw [commRingCatIso_inv_hom_apply (ch.stalkCompAIso y) b] at h
    exact h
  have hnat := (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso
      (ModuleCat.restrictScalars.{u} (ch.stalkCompAIso y).inv.hom)
      (ModuleCat.restrictScalars.{u} (specGermRingHom ch.A (Spec.map ch.c y)))
      (ModuleCat.restrictScalars.{u} (ch.toStalkA y))
      (ModuleCat.restrictScalarsComp'.{u} (specGermRingHom ch.A (Spec.map ch.c y))
        (ch.stalkCompAIso y).inv.hom (ch.toStalkA y) rfl).symm).hom.naturality
    (b • 𝟙 ((derivedStalkFunctor (g' (ch.incU' y))).obj K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  have h₁ := CategoryTheory.Functor.map_comp
    (ModuleCat.restrictScalars.{u}
      (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory
    (ch.germDerivedStalkSectionsIso y K hK).hom
    ((ModuleCat.restrictScalars.{u, u, u}
      (ch.stalkCompAIso y).inv.hom).mapDerivedCategory.map
      (b • 𝟙 ((derivedStalkFunctor (g' (ch.incU' y))).obj K)))
  have h₂ := CategoryTheory.Functor.map_comp
    (ModuleCat.restrictScalars.{u}
      (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory
    ((ch.stalkCompAIso y).hom.hom b • 𝟙 ((totalDerivedExtensionScalars.{u, u, u}
      (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
      ((affineDerivedSections ch.incU).obj K)))
    (ch.germDerivedStalkSectionsIso y K hK).hom
  exact CategoryTheory.comp_comm_of_comm_comm _ _ _ _ _
    (h₂.symm.trans ((congrArg (ModuleCat.restrictScalars.{u}
      (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.map
      (hcentral.trans (congrArg (fun t => (ch.germDerivedStalkSectionsIso y K hK).hom ≫ t)
        hQ.symm))).trans h₁)) hnat

/-- **Steps six to eight of the source identification are equivariant for the two factors.**
The inverse of the comparison of the two readings of the base-change cohomology, followed by the
base change of the germ identification of the derived sections of the chart and by the cohomology
of the source identification of the cube, carries the action of the left tensor factor
`𝒪_{Spec 𝒪_X(U), q}` of `𝒪_{Spec 𝒪_X(U), q} ⊗_{𝒪_S(V)} 𝒪_{S', f' x'}` to that of the left factor
`𝒪_{X, g' x'}` of `𝒪_{X, g' x'} ⊗_{𝒪_{S, s}} 𝒪_{S', s'}`, and the action of the right factor to
that of the right factor.

The left factor is the delicate one: the scalar acts on the source through the local ring of
`Spec 𝒪_X(U)` and on the target through the local ring of `X`, and what reconciles the two is
`AlgebraicGeometry.BaseChangeChart.restrictGermDerivedStalkSectionsIso_smul_comm`. -/
public theorem localRingsSourceIso_restrictMap_inv_smul
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) (b : ToType (X.presheaf.stalk (g' (ch.incU' y))))
    (r : ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A
        (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ ξ : (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((ModuleCat.restrictScalars.{u}
            (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
            ((affineDerivedSections ch.incU).obj K))) n : Type u),
      ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
            ((ch.localRingsSourceIso y w).hom.app
              ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom
          ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
              (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
              (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom
            ((asIso (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R)
                (A := ch.A) (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
                (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                ((totalDerivedExtensionScalars.{u, u, u}
                  (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                  ((affineDerivedSections ch.incU).obj K)))).inv.hom
              ((Algebra.TensorProduct.includeRight r :
                  ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R]
                    ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
                ((Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R)
                    ((ch.stalkCompAIso y).hom.hom b) :
                      ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R]
                        ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
                  (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
                      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                      ((totalDerivedExtensionScalars.{u, u, u}
                          (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                        ((affineDerivedSections ch.incU).obj K)) n : Type u) from
                    (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R)
                      (A := ch.A)
                      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
                      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                      ((totalDerivedExtensionScalars.{u, u, u}
                        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                        ((affineDerivedSections ch.incU).obj K))).hom ξ))))) =
        (Algebra.TensorProduct.includeRight r :
            ToType (X.presheaf.stalk (g' (ch.incU' y)))
              ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
              ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
          ((Algebra.TensorProduct.includeLeft
              (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
              (S := ToType (S.presheaf.stalk (f (g' (ch.incU' y))))) b :
                ToType (X.presheaf.stalk (g' (ch.incU' y)))
                  ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
                  ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
            (show (RingTheory.TorIndependence.baseChangeCohomology
                (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
                (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n : Type u) from
              ((DerivedCategory.homologyFunctor
                      (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
                    ((ch.localRingsSourceIso y w).hom.app
                      ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom
                ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
                  (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                  (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom ξ))) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  let := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A
      (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro ξ
  have h6R := ModuleCat.inv_comm_of_hom_comm
    (asIso (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R) (A := ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
      ((totalDerivedExtensionScalars.{u, u, u}
        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
        ((affineDerivedSections ch.incU).obj K))))
    (fun z => (Algebra.TensorProduct.includeRight r :
        ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
      (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((ModuleCat.restrictScalars.{u}
            (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
            ((affineDerivedSections ch.incU).obj K))) n : Type u) from z))
    (fun z => (Algebra.TensorProduct.includeRight r :
        ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R]
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
      (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((totalDerivedExtensionScalars.{u, u, u}
          (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
          ((affineDerivedSections ch.incU).obj K)) n : Type u) from z))
    (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap_includeRight_smul
      (R := ch.R) (A := ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
      ((totalDerivedExtensionScalars.{u, u, u}
        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
        ((affineDerivedSections ch.incU).obj K)) r)
  have h6L := ModuleCat.inv_comm_of_hom_comm
    (asIso (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R) (A := ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
      ((totalDerivedExtensionScalars.{u, u, u}
        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
        ((affineDerivedSections ch.incU).obj K))))
    (fun z => (RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
        ((ModuleCat.restrictScalars.{u}
            (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.map
          ((ch.stalkCompAIso y).hom.hom b • 𝟙
            ((totalDerivedExtensionScalars.{u, u, u}
              (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
              ((affineDerivedSections ch.incU).obj K))))).hom z)
    (fun z => (Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R)
        ((ch.stalkCompAIso y).hom.hom b) :
          ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R]
            ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
      (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((totalDerivedExtensionScalars.{u, u, u}
          (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
          ((affineDerivedSections ch.incU).obj K)) n : Type u) from z))
    (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap_smul
      (R := ch.R) (A := ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
      ((totalDerivedExtensionScalars.{u, u, u}
        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
        ((affineDerivedSections ch.incU).obj K))
      ((ch.stalkCompAIso y).hom.hom b))
  have hcompBCM : ∀ {Z₁ Z₂ Z₃ : DerivedCategory (ModuleCat.{u} ch.A)} (α : Z₁ ⟶ Z₂) (β : Z₂ ⟶ Z₃)
      (t : (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) Z₁ n : Type u)),
      (RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n (α ≫ β)).hom t =
        (RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n β).hom
          ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n α).hom t) :=
    fun α β t => congrArg (fun ζ => ModuleCat.Hom.hom ζ t)
      ((RingTheory.TorIndependence.baseChangeCohomologyFunctor (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n).map_comp α β)
  have h7L := fun t => ((hcompBCM _ _ t).symm.trans
      (congrArg (fun φ => (RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n φ).hom t)
        (ch.restrictGermDerivedStalkSectionsIso_smul_comm y K hK b))).trans
    (hcompBCM _ _ t)
  have e6 := (h6L (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      ((totalDerivedExtensionScalars.{u, u, u}
        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
        ((affineDerivedSections ch.incU).obj K)) n : Type u) from
    (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R) (A := ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
      ((totalDerivedExtensionScalars.{u, u, u}
        (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
        ((affineDerivedSections ch.incU).obj K))).hom ξ)).trans
    (congrArg (fun z => (RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
        ((ModuleCat.restrictScalars.{u}
            (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.map
          ((ch.stalkCompAIso y).hom.hom b • 𝟙
            ((totalDerivedExtensionScalars.{u, u, u}
              (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
              ((affineDerivedSections ch.incU).obj K))))).hom z)
      (ModuleCat.iso_inv_hom_apply (asIso
        (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R) (A := ch.A)
          (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
          ((totalDerivedExtensionScalars.{u, u, u}
            (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
            ((affineDerivedSections ch.incU).obj K)))) ξ))
  have e4 := (h6R ((Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R)
      ((ch.stalkCompAIso y).hom.hom b) :
        ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R]
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
    (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((totalDerivedExtensionScalars.{u, u, u}
          (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
          ((affineDerivedSections ch.incU).obj K)) n : Type u) from
      (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R) (A := ch.A)
        (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
        ((totalDerivedExtensionScalars.{u, u, u}
          (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
          ((affineDerivedSections ch.incU).obj K))).hom ξ))).trans
    (congrArg (fun z => (Algebra.TensorProduct.includeRight r :
        ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
      (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((ModuleCat.restrictScalars.{u}
            (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
            ((affineDerivedSections ch.incU).obj K))) n : Type u) from z)) e6)
  have e7 := ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
      (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom.map_smul
      (Algebra.TensorProduct.includeRight r)
      ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
        ((ModuleCat.restrictScalars.{u}
          (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.map
          ((ch.stalkCompAIso y).hom.hom b • 𝟙
            ((totalDerivedExtensionScalars.{u, u, u}
              (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
              ((affineDerivedSections ch.incU).obj K))))).hom ξ)).trans
    (congrArg (fun z => (Algebra.TensorProduct.includeRight r :
        ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
      (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K)) n : Type u) from z))
      (h7L ξ))
  have e8 := (ch.localRingsSourceIso_homology_includeRight_smul y w n
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K) r
      ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
        ((ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.map
          (b • 𝟙 ((derivedStalkFunctor (g' (ch.incU' y))).obj K)))).hom
        ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
          (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom ξ))).trans
    (congrArg (fun z => (Algebra.TensorProduct.includeRight r :
        ToType (X.presheaf.stalk (g' (ch.incU' y)))
          ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
      (show (RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n : Type u) from z))
      (ch.localRingsSourceIso_homology_smul y w n
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) b
        ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
          (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom ξ)))
  exact (congrArg (fun z => ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
        ((ch.localRingsSourceIso y w).hom.app
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom
      ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
        (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom z)) e4).trans
    ((congrArg (fun z => ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
          ((ch.localRingsSourceIso y w).hom.app
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom z) e7).trans e8)

/-- **The `𝒪_X(U)` corner move on a pure tensor.** On `x ⊗ (c · ζ)`,
`AlgebraicGeometry.BaseChangeChart.germBaseChangeCohomologyIso` is the action of `x` through the
left tensor factor and of `c` through the right one, on the image of `ζ` under the base change of
the unit of the derived change-of-rings adjunction followed by the comparison of the two readings
of the base-change cohomology.

The corner move is the transpose of that composite along `𝒪_X(U) → 𝒪_{Spec 𝒪_X(U), q}`, by
`RingTheory.TorIndependence.localizedBaseChangeCohomologyComparison_app_eq_transpose`, so the
left factor comes out by `ModuleCat.extendScalarsTranspose_smul_one_tmul` and the right one by
`RingTheory.TorIndependence.baseChangeCohomologyUnitNatTrans_app_includeRight_smul`. -/
public theorem germBaseChangeCohomologyIso_hom_tmul_includeRight_smul
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (K : DerivedCategory X.Modules) (n : ℤ)
    (x : ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
    (r : ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A
        (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Module ch.A (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((affineDerivedSections ch.incU).obj K) n) :=
      Module.compHom _ (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
    ∀ ζ : (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((affineDerivedSections ch.incU).obj K) n : Type u),
      (ch.germBaseChangeCohomologyIso y K n).hom.hom
          (x ⊗ₜ[ch.A] ((Algebra.TensorProduct.includeRight r :
            ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • ζ)) =
        (Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) x :
            ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R]
              ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
          ((Algebra.TensorProduct.includeRight r :
              ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R]
                ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
            (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
                (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                ((totalDerivedExtensionScalars.{u, u, u}
                    (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                  ((affineDerivedSections ch.incU).obj K)) n : Type u) from
              (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R)
                  (A := ch.A) (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
                  (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                  ((totalDerivedExtensionScalars.{u, u, u}
                    (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                    ((affineDerivedSections ch.incU).obj K))).hom
                ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
                    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                    ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ch.A)
                      (A₂ := ToType ((Spec ch.A).presheaf.stalk
                        (Spec.map ch.c y)))).unit.app
                      ((affineDerivedSections ch.incU).obj K))).hom ζ))) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  let := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A
      (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module ch.A (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      ((affineDerivedSections ch.incU).obj K) n) :=
    Module.compHom _ (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
  intro ζ
  have h1 := ModuleCat.extendScalars_tmul_eq_smul_one_tmul
    (specGermRingHom ch.A (Spec.map ch.c y))
    ((ModuleCat.restrictScalars.{u} (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).obj
      (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((affineDerivedSections ch.incU).obj K) n)) x
    ((Algebra.TensorProduct.includeRight r :
      ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • ζ)
  have h2 := ModuleCat.extendScalarsTranspose_smul_one_tmul
    (specGermRingHom ch.A (Spec.map ch.c y))
    ((RingTheory.TorIndependence.baseChangeCohomologyUnitNatTrans (R := ch.R) (A := ch.A)
      (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n).app
      ((affineDerivedSections ch.incU).obj K)) x
    ((Algebra.TensorProduct.includeRight r :
      ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • ζ)
  have h3 := RingTheory.TorIndependence.baseChangeCohomologyUnitNatTrans_app_includeRight_smul
    (R := ch.R) (A := ch.A)
    (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
    ((affineDerivedSections ch.incU).obj K) r ζ
  exact ((congrArg (ch.germBaseChangeCohomologyIso y K n).hom.hom h1).trans h2).trans
    (congrArg (fun t => (Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) x :
        ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R]
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
      (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          ((totalDerivedExtensionScalars.{u, u, u}
              (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
            ((affineDerivedSections ch.incU).obj K)) n : Type u) from t)) h3)

/-- **The `𝒪_{S'}(V')` corner move, inverted, on a pure tensor.** `c ⊗ m` is `c` times
`1 ⊗ m`, and the corner move is `𝒪_{S', f' x'}`-linear, so its inverse carries `c ⊗ m` to the
action of the right tensor factor `c` on the image of `1 ⊗ m`. -/
public theorem homologyBaseChangeLocalizedIso_inv_tmul
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (K : DerivedCategory X.Modules) (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    ∀ (c : ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        (m : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
          ((affineDerivedSections ch.incU).obj K) n : Type u)),
        (ch.homologyBaseChangeLocalizedIso y K n).inv.hom (c ⊗ₜ[ch.R', ch.toStalkR' y] m) =
          (Algebra.TensorProduct.includeRight c :
              ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
            (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
              (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ((affineDerivedSections ch.incU).obj K) n : Type u) from
              (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
                ((1 : ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                  ⊗ₜ[ch.R', ch.toStalkR' y] m)) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  intro c m
  have h1 := ModuleCat.extendScalars_tmul_eq_smul_one_tmul (ch.toStalkR' y)
    (RingTheory.TorIndependence.baseChangeCohomologyOverBase (R := ch.R) (R' := ch.R')
      ((affineDerivedSections ch.incU).obj K) n) c m
  exact ((congrArg (ch.homologyBaseChangeLocalizedIso y K n).inv.hom h1).trans
      (map_smul (ch.homologyBaseChangeLocalizedIso y K n).inv.hom c _)).trans
    (RingTheory.TorIndependence.baseChangeCohomology_includeRight_smul
      (R := ch.R) (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      ((affineDerivedSections ch.incU).obj K) n c _).symm

/-- **The `𝒪_{S'}(V')` corner move of the chart, as an `𝒪_X(U)`-linear identification.** The
corner move `AlgebraicGeometry.BaseChangeChart.homologyBaseChangeLocalizedIso`, composed with the
commutation of the two tensor factors, identifies

`H^n(RΓ(U,K)|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V')) ⊗_{𝒪_{S'}(V')} 𝒪_{S', s'}`

with `H^n(RΓ(U,K)|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S', s'})`, and the identification is linear over
`𝒪_X(U)` acting through the left tensor factor on both sides. That linearity is
`AlgebraicGeometry.BaseChangeChart.homologyBaseChangeLocalizedIso_hom_includeLeft_smul`
transported to the inverse by `ModuleCat.inv_comm_of_hom_comm`. -/
public theorem exists_localRingsSourceCornerEquiv
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (K : DerivedCategory X.Modules) (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI : Module ch.R' (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
        (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n) :=
      inferInstanceAs (Module ch.R' (RingTheory.TorIndependence.baseChangeCohomologyOverBase
        (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n))
    letI : Module ch.A (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
        (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n) :=
      Module.compHom _ (algebraMap ch.A (ch.A ⊗[ch.R] ch.R'))
    letI : Module ch.A (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ((affineDerivedSections ch.incU).obj
            K) n) :=
      Module.compHom _ (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A (ToType
          (S'.presheaf.stalk (f' (ch.incU' y)))))
    ∃ e₀ : ((RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
          (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n : Type u) ⊗[ch.R']
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ≃+
        (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          ((affineDerivedSections ch.incU).obj K) n : Type u),
      (∀ (x : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
            ((affineDerivedSections ch.incU).obj K) n : Type u))
          (c : ToType (S'.presheaf.stalk (f' (ch.incU' y)))),
          e₀ (x ⊗ₜ[ch.R'] c) = (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
            (c ⊗ₜ[ch.R', ch.toStalkR' y] x)) ∧
        ∀ (a : ch.A) (m : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
            (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n : Type u))
          (c : ToType (S'.presheaf.stalk (f' (ch.incU' y)))),
          e₀ ((a • m) ⊗ₜ[ch.R'] c) = a • e₀ (m ⊗ₜ[ch.R'] c) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let : Module ch.R' (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
      (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n) :=
    inferInstanceAs (Module ch.R' (RingTheory.TorIndependence.baseChangeCohomologyOverBase
      (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n))
  let : Module ch.A (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
      (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n) :=
    Module.compHom _ (algebraMap ch.A (ch.A ⊗[ch.R] ch.R'))
  let : Module ch.A (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ((affineDerivedSections ch.incU).obj K)
          n) :=
    Module.compHom _ (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A (ToType
        (S'.presheaf.stalk (f' (ch.incU' y)))))
  obtain ⟨e₀, hcoe⟩ : ∃ e₀ : ((RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
          (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n : Type u) ⊗[ch.R']
          ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ≃+
        (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          ((affineDerivedSections ch.incU).obj K) n : Type u),
        ∀ (x : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
            ((affineDerivedSections ch.incU).obj K) n : Type u))
          (c : ToType (S'.presheaf.stalk (f' (ch.incU' y)))),
          e₀ (x ⊗ₜ[ch.R'] c) = (ch.homologyBaseChangeLocalizedIso y K n).inv.hom
            (c ⊗ₜ[ch.R', ch.toStalkR' y] x) := by
    refine ⟨(TensorProduct.comm ch.R'
        (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
          ((affineDerivedSections ch.incU).obj K) n : Type u)
        (ToType (S'.presheaf.stalk (f' (ch.incU' y))))).toAddEquiv.trans
      (ch.homologyBaseChangeLocalizedIso y K n).symm.toLinearEquiv.toAddEquiv, fun x c => ?_⟩
    change (ch.homologyBaseChangeLocalizedIso y K n).symm.toLinearEquiv
      (TensorProduct.comm ch.R'
        (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
          ((affineDerivedSections ch.incU).obj K) n : Type u)
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) (x ⊗ₜ[ch.R'] c)) = _
    rw [TensorProduct.comm_tmul]
    rfl
  have hact : ∀ (a : ch.A)
      (m : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
        (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n : Type u)),
      a • m = ((RingTheory.TorIndependence.derivedBaseChangeFunctor (R := ch.R) (A := ch.A)
          (R' := ch.R') ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).map
        (a • 𝟙 ((affineDerivedSections ch.incU).obj K))).hom m := fun a m =>
    (RingTheory.TorIndependence.baseChangeCohomologyModuleGeneral_includeLeft_smul
        (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n a m).trans
      (RingTheory.TorIndependence.baseChangeCohomologyActionGeneral_apply_eq
        (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n a m)
  have he₀ : ∀ (a : ch.A)
      (m : (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
        (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n : Type u))
      (c : ToType (S'.presheaf.stalk (f' (ch.incU' y)))),
      e₀ ((a • m) ⊗ₜ[ch.R'] c) = a • e₀ (m ⊗ₜ[ch.R'] c) := by
    intro a m c
    have key := ModuleCat.inv_comm_of_hom_comm (ch.homologyBaseChangeLocalizedIso y K n)
      (fun z => (Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) a :
          ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
        (show (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          ((affineDerivedSections ch.incU).obj K) n : Type u) from z))
      (fun w => ((ModuleCat.extendScalars.{u, u, u} (ch.toStalkR' y)).map
          ((RingTheory.TorIndependence.derivedBaseChangeFunctor (R := ch.R) (A := ch.A)
              (R' := ch.R') ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).map
            (a • 𝟙 ((affineDerivedSections ch.incU).obj K)))).hom w)
      (ch.homologyBaseChangeLocalizedIso_hom_includeLeft_smul y K n a)
      (c ⊗ₜ[ch.R', ch.toStalkR' y] m)
    have hmap := ModuleCat.ExtendScalars.map_tmul (ch.toStalkR' y)
      ((RingTheory.TorIndependence.derivedBaseChangeFunctor (R := ch.R) (A := ch.A)
          (R' := ch.R') ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).map
        (a • 𝟙 ((affineDerivedSections ch.incU).obj K))) c m
    rw [hcoe, hcoe, hact a m]
    exact (congrArg (ch.homologyBaseChangeLocalizedIso y K n).inv.hom hmap.symm).trans key
  exact ⟨e₀, hcoe, he₀⟩

/-- **The source identification of the cube at a chart, as a bijection of the two sources.**
The germ comparison of the local rings of `X`, the `𝒪_X(U)` corner move on cohomology, the
comparison of the two readings of the base-change cohomology, the base change of the germ
identification of the derived sections and the cohomology of the source identification of the
cube compose to a bijection

`𝒪_{X, g' x'} ⊗_{𝒪_X(U)} H^n(RΓ(U,K)|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S', s'})  ≅
  H^n(K_{g' x'}|_{𝒪_{S, s}} ⊗ᴸ_{𝒪_{S, s}} 𝒪_{S', s'})`

whose value on `b ⊗ (c · ζ)` is `b ⊗ c` times the formula of
`AlgebraicGeometry.BaseChangeChart.localRingsSourceMap` at `ζ`. Every step is an isomorphism, so
the composite is one; the content is the formula, which is
`Stacks.TensorProductPushout.baseCongr_tmul` followed by
`AlgebraicGeometry.BaseChangeChart.germBaseChangeCohomologyIso_hom_tmul_includeRight_smul` and
`AlgebraicGeometry.BaseChangeChart.localRingsSourceIso_restrictMap_inv_smul`. -/
public theorem exists_localRingsSourceComposite
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Module ch.A (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ((affineDerivedSections ch.incU).obj
            K) n) :=
      Module.compHom _ (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
    ∃ Ξ : (ToType (X.presheaf.stalk (g' (ch.incU' y))) ⊗[ch.A]
        (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ((affineDerivedSections
              ch.incU).obj K) n : Type u)) →
        (RingTheory.TorIndependence.baseChangeCohomology (R := ToType (S.presheaf.stalk (f (g'
            (ch.incU' y)))))
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ((derivedStalkFunctor (g' (ch.incU'
              y))).obj K) n : Type u),
      (∀ z z', Ξ (z + z') = Ξ z + Ξ z') ∧ Function.Bijective Ξ ∧
        ∀ (b : ToType (X.presheaf.stalk (g' (ch.incU' y)))) (r : ToType (S'.presheaf.stalk (f'
            (ch.incU' y))))
          (ζ : (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ((affineDerivedSections
                ch.incU).obj K) n : Type u)),
          Ξ (b ⊗ₜ[ch.A] ((Algebra.TensorProduct.includeRight r :
              ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • ζ)) =
            (Algebra.TensorProduct.includeRight r :
                ToType (X.presheaf.stalk (g' (ch.incU' y))) ⊗[ToType (S.presheaf.stalk (f (g'
                    (ch.incU' y))))] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
              ((Algebra.TensorProduct.includeLeft (R := ToType (S.presheaf.stalk (f (g' (ch.incU'
                  y)))))
                  (S := ToType (S.presheaf.stalk (f (g' (ch.incU' y))))) b :
                    ToType (X.presheaf.stalk (g' (ch.incU' y))) ⊗[ToType (S.presheaf.stalk (f (g'
                        (ch.incU' y))))] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
                (show (RingTheory.TorIndependence.baseChangeCohomology (R := ToType
                    (S.presheaf.stalk (f (g' (ch.incU' y)))))
                    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ((derivedStalkFunctor (g'
                        (ch.incU' y))).obj K) n : Type u) from
                  ((DerivedCategory.homologyFunctor
                      (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
                    ((ch.localRingsSourceIso y w).hom.app ((derivedStalkFunctor (g' (ch.incU'
                        y))).obj K))).hom
                    ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
                        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                        (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom
                      ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
                          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                        ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ch.A)
                          (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
                              ((affineDerivedSections ch.incU).obj K))).hom ζ)))) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  let := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module ch.A (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ((affineDerivedSections ch.incU).obj K)
          n) :=
    Module.compHom _ (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
  have : IsIso (RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
      (ch.restrictGermDerivedStalkSectionsIso y K hK).hom) :=
    inferInstanceAs (IsIso ((RingTheory.TorIndependence.baseChangeCohomologyFunctor (R := ch.R)
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
      (ch.restrictGermDerivedStalkSectionsIso y K hK).hom))
  refine ⟨fun z => ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
      ((ch.localRingsSourceIso y w).hom.app
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom
    ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
        (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom
      ((asIso (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R)
          (A := ch.A) (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
          ((totalDerivedExtensionScalars.{u, u, u}
            (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
            ((affineDerivedSections ch.incU).obj K)))).inv.hom
        ((ch.germBaseChangeCohomologyIso y K n).hom.hom
          (Stacks.TensorProductPushout.baseCongr (A := ch.A)
            (M := (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
              (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ((affineDerivedSections ch.incU).obj K) n : Type u))
            (ch.stalkCompAIso y).hom.hom (ch.stalkCompAIso y).inv.hom
            (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
            (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y))
            (fun a => commRingCatIso_hom_inv_apply (ch.stalkCompAIso y)
              (specGermRingHom ch.A (Spec.map ch.c y) a)) z)))), ?_, ?_, ?_⟩
  · intro z z'
    exact (congrArg (fun t => ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
          ((ch.localRingsSourceIso y w).hom.app
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom
          ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
             (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
             (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom
            ((asIso (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R)
               (A := ch.A) (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
               (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
               ((totalDerivedExtensionScalars.{u, u, u}
                 (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                 ((affineDerivedSections ch.incU).obj K)))).inv.hom
              ((ch.germBaseChangeCohomologyIso y K n).hom.hom t))))
        (map_add (Stacks.TensorProductPushout.baseCongr (A := ch.A)
           (M := (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
             (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
             ((affineDerivedSections ch.incU).obj K) n : Type u))
           (ch.stalkCompAIso y).hom.hom (ch.stalkCompAIso y).inv.hom
           (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
           (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y))
           (fun a => commRingCatIso_hom_inv_apply (ch.stalkCompAIso y)
             (specGermRingHom ch.A (Spec.map ch.c y) a))) z z')).trans
      ((congrArg (fun t => ((DerivedCategory.homologyFunctor
             (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
           ((ch.localRingsSourceIso y w).hom.app
             ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom
            ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
               (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
               (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom
              ((asIso (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R)
                 (A := ch.A) (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
                 (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                 ((totalDerivedExtensionScalars.{u, u, u}
                   (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                   ((affineDerivedSections ch.incU).obj K)))).inv.hom t)))
          (map_add (ch.germBaseChangeCohomologyIso y K n).hom.hom _ _)).trans
        ((congrArg (fun t => ((DerivedCategory.homologyFunctor
              (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
            ((ch.localRingsSourceIso y w).hom.app
              ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom
              ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
                 (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                 (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom t))
            (map_add (asIso (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R)
               (A := ch.A) (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
               (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
               ((totalDerivedExtensionScalars.{u, u, u}
                 (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                 ((affineDerivedSections ch.incU).obj K)))).inv.hom _ _)).trans
          ((congrArg (fun t => ((DerivedCategory.homologyFunctor
               (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
             ((ch.localRingsSourceIso y w).hom.app
               ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom t)
              (map_add (RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
                 (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
                 (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom _ _)).trans
            (map_add ((DerivedCategory.homologyFunctor
                 (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
               ((ch.localRingsSourceIso y w).hom.app
                 ((derivedStalkFunctor (g' (ch.incU' y))).obj K))).hom _ _))))
  · exact ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).comp
      (((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).comp
        (((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).comp
          (((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).comp
            (LinearEquiv.bijective _))))
  · intro b r ζ
    have hswap : ∀ t : (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) ((totalDerivedExtensionScalars.{u, u,
            u}
          (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
          ((affineDerivedSections ch.incU).obj K)) n : Type u),
        (Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R)
            ((ch.stalkCompAIso y).hom.hom b) :
              ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R] ToType
                  (S'.presheaf.stalk (f' (ch.incU' y)))) •
          ((Algebra.TensorProduct.includeRight r :
            ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R] ToType
                (S'.presheaf.stalk (f' (ch.incU' y)))) • t) =
          (Algebra.TensorProduct.includeRight r :
              ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R] ToType
                  (S'.presheaf.stalk (f' (ch.incU' y)))) •
            ((Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R)
              ((ch.stalkCompAIso y).hom.hom b) :
                ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R] ToType
                    (S'.presheaf.stalk (f' (ch.incU' y)))) • t) := by
      intro t
      rw [smul_smul, smul_smul, mul_comm]
    exact (congrArg (fun z => ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).map
          ((ch.localRingsSourceIso y w).hom.app ((derivedStalkFunctor (g' (ch.incU' y))).obj
              K))).hom
          ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
              (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
              (ch.restrictGermDerivedStalkSectionsIso y K hK).hom).hom
            ((asIso (RingTheory.TorIndependence.baseChangeCohomologyRestrictMap (R := ch.R)
               (A := ch.A) (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
               (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
               ((totalDerivedExtensionScalars.{u, u, u}
               (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
               ((affineDerivedSections ch.incU).obj K)))).inv.hom z)))
        (((congrArg (ch.germBaseChangeCohomologyIso y K n).hom.hom
            (Stacks.TensorProductPushout.baseCongr_tmul (A := ch.A)
              (M := (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
                (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                ((affineDerivedSections ch.incU).obj K) n : Type u))
              (ch.stalkCompAIso y).hom.hom (ch.stalkCompAIso y).inv.hom
              (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
              (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y))
              (fun a => commRingCatIso_hom_inv_apply (ch.stalkCompAIso y)
                (specGermRingHom ch.A (Spec.map ch.c y) a)) b
              ((Algebra.TensorProduct.includeRight r :
                ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • ζ))).trans
          (ch.germBaseChangeCohomologyIso_hom_tmul_includeRight_smul y K n
            ((ch.stalkCompAIso y).hom.hom b) r ζ)).trans (hswap _))).trans
      (ch.localRingsSourceIso_restrictMap_inv_smul y w K hK n b r
        ((RingTheory.TorIndependence.baseChangeCohomologyMap (R := ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y)))) n
          ((RingTheory.TorIndependence.derivedExtendRestrictAdjunction (A := ch.A)
            (A₂ := ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))).unit.app
                ((affineDerivedSections ch.incU).obj K))).hom ζ))

/-- **The source identification of the cube at a chart is bijective.** Transposed along
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V') → 𝒪_{X,g'x'} ⊗_{𝒪_{S,s}} 𝒪_{S',s'}`,
`AlgebraicGeometry.BaseChangeChart.localRingsSourceMap` is a bijection between the source of the
germ-localized chart map of condition (2) of Stacks 0DJ8 and the source of the pointwise map of
Stacks 0DJ7 at the corresponding point of `X'`.

The transposing map is taken abstractly, pinned only by its values on the generators `1 ⊗ m`:
that is all the final assembly has, and it keeps the statement independent of how the map is
built there. The bijectivity is
`ModuleCat.bijective_extendScalarsTranspose_of_rearrange` applied to the two base changes the
extension of scalars splits into, which are
`AlgebraicGeometry.BaseChangeChart.exists_localRingsSourceCornerEquiv` and
`AlgebraicGeometry.BaseChangeChart.exists_localRingsSourceComposite`. -/
public theorem bijective_extendScalarsTranspose_localRingsSourceMap
    (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules)
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K).IsQuasicoherent)
    (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR y).toAlgebra
    letI := (ch.toStalkA y).toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
    letI := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
    haveI : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
    letI : Algebra (ch.A ⊗[ch.R] ch.R')
        (ToType (X.presheaf.stalk (g' (ch.incU' y))) ⊗[ToType (S.presheaf.stalk
          (f (g' (ch.incU' y))))] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
      Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
        (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
        (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    ∀ v : RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
          ((affineDerivedSections ch.incU).obj K) n ⟶
        (ModuleCat.restrictScalars.{u} (algebraMap (ch.A ⊗[ch.R] ch.R')
            (ToType (X.presheaf.stalk (g' (ch.incU' y))) ⊗[ToType (S.presheaf.stalk
              (f (g' (ch.incU' y))))] ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).obj
          (RingTheory.TorIndependence.baseChangeCohomology
            (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n),
      (∀ m, v.hom m = ch.localRingsSourceMap y w K hK n m) →
        Function.Bijective (ModuleCat.extendScalarsTranspose
          (algebraMap (ch.A ⊗[ch.R] ch.R')
            (ToType (X.presheaf.stalk (g' (ch.incU' y))) ⊗[ToType (S.presheaf.stalk
              (f (g' (ch.incU' y))))] ToType (S'.presheaf.stalk (f' (ch.incU' y))))) v).hom := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR y).toAlgebra
  let := (ch.toStalkA y).toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := (f.stalkMap (g' (ch.incU' y))).hom.toAlgebra
  let := (baseStalkMap f g f' g' w (ch.incU' y)).toAlgebra
  let := ((ch.toStalkA y).comp ch.a.hom).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  have : IsScalarTower ch.R ch.A (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (X.presheaf.stalk (g' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkA_a y)
  have : IsScalarTower ch.R ch.R' (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower ch.R (ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    IsScalarTower.of_algebraMap_eq' (ch.toStalkR'_b y w).symm
  let : Algebra (ch.A ⊗[ch.R] ch.R')
      (ToType (X.presheaf.stalk (g' (ch.incU' y))) ⊗[ToType (S.presheaf.stalk
        (f (g' (ch.incU' y))))] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :=
    Stacks.TensorProductPushout.mapAlgebraMid (R := ch.R) (A := ch.A) (R' := ch.R')
      (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
      (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
      (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
  let : Module ch.R' (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
      (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n) :=
    inferInstanceAs (Module ch.R' (RingTheory.TorIndependence.baseChangeCohomologyOverBase
      (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n))
  let : Module ch.A (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
      (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n) :=
    Module.compHom _ (algebraMap ch.A (ch.A ⊗[ch.R] ch.R'))
  have : IsScalarTower ch.A (ch.A ⊗[ch.R] ch.R')
      (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower ch.R' (ch.A ⊗[ch.R] ch.R')
      (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) n) :=
    IsScalarTower.of_algebraMap_smul fun r m =>
      RingTheory.TorIndependence.baseChangeCohomologyModuleGeneral_includeRight_smul
        (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n r m
  have := Stacks.TensorProductPushout.smulCommClass_of_tensorTower (A := ch.A) (R' := ch.R')
    (M := (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
      ((affineDerivedSections ch.incU).obj K) n : Type u)) ch.R
  let : Module ch.A (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      ((affineDerivedSections ch.incU).obj K) n) :=
    Module.compHom _ (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  let := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have := ch.isLocalization_toStalkR y
  intro v hv
  obtain ⟨e₀, hcoe, he₀⟩ := ch.exists_localRingsSourceCornerEquiv y K n
  obtain ⟨Ξ, hΞadd, hΞbij, hΞgen⟩ := ch.exists_localRingsSourceComposite y w K hK n
  have hz := ch.homologyBaseChangeLocalizedIso_inv_tmul y K n
  refine ModuleCat.bijective_extendScalarsTranspose_of_rearrange
    (R := ch.R) (A := ch.A) (R' := ch.R')
    (Rp := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
    (B := ToType (X.presheaf.stalk (g' (ch.incU' y))))
    (C := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
    (M := RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R) (R' := ch.R')
      ((affineDerivedSections ch.incU).obj K) n)
    (G := (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
      (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
      ((affineDerivedSections ch.incU).obj K) n : Type u))
    (instA := IsScalarTower.of_algebraMap_smul fun _ _ => rfl)
    (instR' := IsScalarTower.of_algebraMap_smul fun r m =>
      RingTheory.TorIndependence.baseChangeCohomologyModuleGeneral_includeRight_smul
        (R := ch.R) (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n r m)
    (instCC := Stacks.TensorProductPushout.smulCommClass_of_tensorTower (A := ch.A)
      (R' := ch.R') (M := (RingTheory.TorIndependence.baseChangeCohomologyCatGeneral (R := ch.R)
        (R' := ch.R') ((affineDerivedSections ch.incU).obj K) n : Type u)) ch.R)
    (ch.primeComplR y) e₀ he₀ v Ξ hΞadd hΞbij (fun b c m => ?_)
  refine ((congrArg (fun t => Ξ (b ⊗ₜ[ch.A] t)) ((hcoe m c).trans (hz c m))).trans
    (hΞgen b c _)).trans ?_
  refine Eq.trans ?_ (((congrArg (fun t => t •
        (show (RingTheory.TorIndependence.baseChangeCohomology
          (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n : Type u) from v.hom m))
      ((RingTheory.TorIndependence.tmul_eq_includeLeft_mul_includeRight b c).trans
        (mul_comm _ _))).trans (mul_smul _ _ _)).symm)
  exact congrArg (fun t => (Algebra.TensorProduct.includeRight c :
      ToType (X.presheaf.stalk (g' (ch.incU' y)))
        ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
        ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
    ((Algebra.TensorProduct.includeLeft
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (S := ToType (S.presheaf.stalk (f (g' (ch.incU' y))))) b :
          ToType (X.presheaf.stalk (g' (ch.incU' y)))
            ⊗[ToType (S.presheaf.stalk (f (g' (ch.incU' y))))]
            ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
      (show (RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' (ch.incU' y)))))
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) n : Type u) from t))) (hv m).symm


end BaseChangeChart

end AlgebraicGeometry

end
