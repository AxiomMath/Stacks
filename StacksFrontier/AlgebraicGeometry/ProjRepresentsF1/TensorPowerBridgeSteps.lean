module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.BundleBridge
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebraMul
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleWitnessOverBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AssociatedSheafPullback

/-!
# The two base cases and the successor law of `TensorPowerBridge`

`Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridge` asks, in each degree `m`, that
the comparison `pullbackTensorPowerIso` of the `m`-fold tensor powers agree, through
`tensorPowerToLaurent`, with the comparison `laurentPullback` of the integral tensor powers of
Tag 01CU. This file supplies the pieces of the induction on `m`.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isEquivalence_tensorRightFunctor_scheme`:
  **tensoring on the right by an invertible module on a scheme is an equivalence**, stated at
  the structure-sheaf spelling the Laurent algebra of Section 01NS uses with the hypothesis at
  the spelling a scheme's sheaves of modules carry.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.laurentGenerator_pullback`: **the degree-one case
  of the bridge.** The degree-one generator of the Laurent algebra commutes with pullback.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorPieceIso_inv_comp_app_add_two`: **the
  left-handed concatenation law for the homogeneous identifications of a tensor algebra, as an
  equation of morphisms**, read through a homomorphism to any graded algebra and stated over an
  arbitrary site: the morphism form of the sectionwise structure field
  `SheafOfModules.TensorExteriorSymmetricAlgebras.tensorPieceIso_mul_left`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorPowerToLaurent_add_two`: **the left-handed
  successor law for `tensorPowerToLaurent`** — the previous result at the comparison of the
  tensor algebra of `L` with its Laurent algebra. The comparison of the `(m+2)`-fold tensor
  power with the degree-`(m+2)` piece of the Laurent algebra is the Laurent generator tensored
  with the comparison in degree `m+1`, followed by the multiplication of the Laurent algebra in
  bidegree `(1, m+1)`.

## Implementation notes

`Stacks.SheafOfModules.TensorPower.tensorPowerOneIso`, and with it the degree-one generator of
the Laurent algebra, takes the instance
`(Stacks.SheafOfModules.TensorPower.tensorRightFunctor O hO L).IsEquivalence`. At a goal about a
scheme the structure sheaf is spelled `T.toRingedSpace.presheaf` and `isSheafStruct T`, while the
module's own type carries `T.presheaf` and `T.ringCatSheaf.2`, and the two are equal by `rfl` but
do not unify at `instance` transparency. `isEquivalence_tensorRightFunctor_scheme` is the same
instance with its conclusion written at the first spelling and its hypothesis at the second.

The successor law is four facts composed: the concatenation law `generatorMul_comp_eq_id` of the
homogeneous identifications of a tensor algebra, as an equation of morphisms; the commutation
`generatorMul_comp_app` of multiplication by a degree-one generator with a homomorphism of graded
algebras; `tensorGenerator_comp_tensorToLaurent`, which says that the comparison of the tensor
algebra with the Laurent algebra carries the tensor generator to the Laurent generator; and
`generatorMul_eq`, which presents multiplication by a generator as the generator tensored into
the graded multiplication — the shape in which
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback_mulSheaf` states the
multiplicativity of `laurentPullback`, in an arbitrary bidegree.

The law is proved over an arbitrary site and specialised by application, and no monoidal notation
appears: `Stacks.SheafOfModules.Tensor.sheafTensor` needs no monoidal instance.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RingedSpace

open scoped TensorProduct

universe v u w

/-! ### The invertibility instance at the scheme spelling -/

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

/-- **Tensoring on the right by an invertible module on a scheme is an equivalence**, at the
structure-sheaf spelling the Laurent algebra of Section 01NS uses and with the hypothesis at the
spelling a scheme's sheaves of modules carry. -/
instance isEquivalence_tensorRightFunctor_scheme (X : Scheme.{u}) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
          ⟨X.toRingedSpace.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ X.toRingedSpace.presheaf
              (forget₂ CommRingCat RingCat) (isSheafStruct X)⟩).flip.obj M)).IsEquivalence :=
  letI : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (isSheafStruct X) M :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry X.toRingedSpace.presheaf
      (isSheafStruct X) M hM
  Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    X.toRingedSpace.presheaf (isSheafStruct X) M

/-! ### Degree one -/

section DegreeOne

variable {T T' : Scheme.{u}} (g : T' ⟶ T) (L : T.Modules)
  [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]

/-- **The degree-one generator of the Laurent algebra commutes with pullback.** The generator is
the inverse of the identification `L^{⊗ 1} = L` of Tag 01CU
(`Stacks.SheafOfModules.TensorPower.tensorPowerOneIso`), and that identification commutes with
pullback through the comparison of the integral tensor powers by
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback_tensorPowerOneIso`; inverting it
on both sides is the whole content.

This is the degree-one case of
`Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridge`, since `pullbackTensorPowerIso` is
`Iso.refl` in degree one and `tensorPowerToLaurent` is the Laurent generator there
(`tensorPowerToLaurent_one`). -/
public theorem laurentGenerator_pullback :
    laurentGenerator ((Scheme.Modules.pullback g).obj L) =
      (Scheme.Modules.pullback g).map (laurentGenerator L) ≫ laurentPullback g L 1 := by
  have hone := laurentPullback_tensorPowerOneIso g L
  conv_lhs => unfold laurentGenerator Stacks.LineBundle.Situation.laurentGen laurentSituation
  show (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso
    T'.toRingedSpace.presheaf (isSheafStruct T') ((Scheme.Modules.pullback g).obj L)).inv = _
  refine ((Iso.comp_hom_eq_id (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso
    T'.toRingedSpace.presheaf (isSheafStruct T')
    ((Scheme.Modules.pullback g).obj L))).mp ?_).symm
  calc ((Scheme.Modules.pullback g).map (laurentGenerator L) ≫ laurentPullback g L 1) ≫
        (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso T'.toRingedSpace.presheaf
          (isSheafStruct T') ((Scheme.Modules.pullback g).obj L)).hom
      = (Scheme.Modules.pullback g).map (laurentGenerator L) ≫
          (laurentPullback g L 1 ≫
            (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso T'.toRingedSpace.presheaf
              (isSheafStruct T') ((Scheme.Modules.pullback g).obj L)).hom) :=
        Category.assoc _ _ _
    _ = (Scheme.Modules.pullback g).map (laurentGenerator L) ≫
          (Scheme.Modules.pullback g).map
            (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso T.toRingedSpace.presheaf
              (isSheafStruct T) L).hom :=
        congrArg (fun z => (Scheme.Modules.pullback g).map (laurentGenerator L) ≫ z) hone.symm
    _ = (Scheme.Modules.pullback g).map (laurentGenerator L ≫
          (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso T.toRingedSpace.presheaf
            (isSheafStruct T) L).hom) :=
        (Functor.map_comp (Scheme.Modules.pullback g) _ _).symm
    _ = (Scheme.Modules.pullback g).map (𝟙 L) :=
        congrArg (Scheme.Modules.pullback g).map
          (Iso.inv_hom_id (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso
            T.toRingedSpace.presheaf (isSheafStruct T) L))
    _ = 𝟙 _ := (Scheme.Modules.pullback g).map_id _

end DegreeOne

/-! ### The left-handed successor law for `tensorPowerToLaurent` -/

/-- A composite of three whose composition with an isomorphism is the identity is the inverse of
that isomorphism. -/
private theorem inv_eq_of_comp_four {D : Type*} [Category D] {W X Y Z : D} {a : W ⟶ X}
    {b : X ⟶ Y} {c : Y ⟶ Z} {i : Z ≅ W} (h : a ≫ b ≫ c ≫ i.hom = 𝟙 W) :
    i.inv = a ≫ b ≫ c :=
  ((Iso.comp_hom_eq_id i).mp
    (Eq.trans (Category.assoc a (b ≫ c) i.hom)
      (Eq.trans (congrArg (fun z => a ≫ z) (Category.assoc b c i.hom)) h))).symm

/-- A degreewise family of morphisms of sheaves of modules commutes with the transport along an
equality of degrees. -/
private theorem eqToHom_comp_app {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {A A' : SheafOfModules.GradedAlgebra.{w, w} R}
    (φ : ∀ n : ℤ, A.piece n ⟶ A'.piece n) {i j : ℤ} (h : i = j) :
    eqToHom (congrArg A.piece h) ≫ φ j = φ i ≫ eqToHom (congrArg A'.piece h) := by
  subst h
  simp

/-- **The rearrangement the successor law is, with every object and morphism free**: six
commuting squares composed into one. -/
private theorem succ_rearrange {D : Type*} [Category D] {W X Y₀ Y₁ Z₁ Z₂ P R : D}
    {iinv : W ⟶ X} {a : W ⟶ Y₀} {gm : Y₀ ⟶ Y₁} {e : Y₁ ⟶ X} (t2 : X ⟶ Z₂) {t1 : Y₁ ⟶ Z₁}
    {q : Z₁ ⟶ Z₂} {b : Y₀ ⟶ P} {n : P ⟶ Z₁} {c : W ⟶ P} {d : P ⟶ R} {mu : R ⟶ Z₁} {f : W ⟶ R}
    (hinv : iinv = a ≫ gm ≫ e) (hdeg : e ≫ t2 = t1 ≫ q) (hstep : gm ≫ t1 = b ≫ n)
    (hmerge : a ≫ b = c) (hgen : n = d ≫ mu) (hmerge2 : c ≫ d = f) :
    iinv ≫ t2 = f ≫ mu ≫ q := by
  calc iinv ≫ t2 = (a ≫ gm ≫ e) ≫ t2 := by rw [hinv]
    _ = a ≫ gm ≫ e ≫ t2 := by simp only [Category.assoc]
    _ = a ≫ gm ≫ t1 ≫ q := by rw [hdeg]
    _ = a ≫ (gm ≫ t1) ≫ q := by simp only [Category.assoc]
    _ = a ≫ (b ≫ n) ≫ q := by rw [hstep]
    _ = (a ≫ b) ≫ n ≫ q := by simp only [Category.assoc]
    _ = c ≫ (d ≫ mu) ≫ q := by rw [hmerge, hgen]
    _ = (c ≫ d) ≫ mu ≫ q := by simp only [Category.assoc]
    _ = f ≫ mu ≫ q := by rw [hmerge2]

section Abstract

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (Sheaf.toRingCat J Osharp)}
  (B : SheafOfModules.TensorExteriorSymmetricAlgebras J F)
  {Lam : SheafOfModules.GradedAlgebra.{w, w} (Sheaf.toRingCat J Osharp)}
  (phi : SheafOfModules.GradedAlgebra.UnitalHom B.tensor Lam)
  {gamma : F ⟶ Lam.piece 1} (hgamma : B.tensorGenerator ≫ phi.app 1 = gamma)

include hgamma in
/-- **The left-handed concatenation law for the homogeneous identifications of a tensor algebra,
read through a homomorphism to another graded algebra.** The degree-`(m+2)` identification
followed by the homomorphism is the degree-one generator `gamma` in the left factor and the
degree-`(m+1)` identification followed by the homomorphism in the right factor, followed by the
multiplication of the target in bidegree `(1, m+1)` and the transport to the total degree.

Three facts compose into it: the concatenation law `generatorMul_comp_eq_id` of the bundle's
homogeneous identifications, the commutation `generatorMul_comp_app` of multiplication by a
degree-one generator with a homomorphism of graded algebras, and `generatorMul_eq`, which
presents multiplication by a generator as the generator tensored into the graded
multiplication. -/
public theorem tensorPieceIso_inv_comp_app_add_two (m : ℕ)
    (hc : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ)) :
    (B.tensorPieceIso (m + 2)).inv ≫ phi.app ((m + 2 : ℕ) : ℤ) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).map gamma).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj _).map
        ((B.tensorPieceIso (m + 1)).inv ≫ phi.app ((m + 1 : ℕ) : ℤ))) ≫
        Lam.mulSheaf 1 ((m + 1 : ℕ) : ℤ) ≫ eqToHom (congrArg Lam.piece hc) :=
  succ_rearrange _
    (inv_eq_of_comp_four (generatorMul_comp_eq_id B m hc))
    (eqToHom_comp_app (fun n => phi.app n) hc)
    ((generatorMul_comp_app phi.toHom B.tensorGenerator ((m + 1 : ℕ) : ℤ)).trans
      (congrArg (fun z =>
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj F).map
            (phi.app ((m + 1 : ℕ) : ℤ)) ≫
          SheafOfModules.GradedAlgebra.generatorMul z ((m + 1 : ℕ) : ℤ)) hgamma))
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj F).map_comp _ _).symm
    (generatorMul_eq (A' := Lam) gamma ((m + 1 : ℕ) : ℤ))
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).map gamma).naturality
      ((B.tensorPieceIso (m + 1)).inv ≫ phi.app ((m + 1 : ℕ) : ℤ)))

end Abstract

section Successor

variable {T : Scheme.{u}} (TA : TensorAlgebras.{u}) (L : T.Modules)
  [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]

/-- **The left-handed successor law for `tensorPowerToLaurent`.** The `(m+2)`-fold tensor power
of `L` is `L` tensored with the `(m+1)`-fold one, and under that presentation the comparison of
the tensor powers with the Laurent algebra in degree `m+2` is the Laurent generator in the left
factor and the comparison in degree `m+1` in the right factor, followed by the multiplication of
the Laurent algebra in bidegree `(1, m+1)` and the transport to the total degree.

This is `tensorPieceIso_inv_comp_app_add_two` at the comparison `tensorToLaurent` of the tensor
algebra of `L` with its Laurent algebra, whose degree-one value is the Laurent generator by
`tensorGenerator_comp_tensorToLaurent`. The bidegree `(1, m+1)` is the one at which
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback_mulSheaf` states the
multiplicativity of the comparison of the integral tensor powers. -/
public theorem tensorPowerToLaurent_add_two (m : ℕ)
    (hc : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ)) :
    tensorPowerToLaurent TA L (m + 2) =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨T.presheaf, T.IsSheaf⟩).map (laurentGenerator L)).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨T.presheaf, T.IsSheaf⟩).obj _).map (tensorPowerToLaurent TA L (m + 1))) ≫
        (laurent L).mulSheaf 1 ((m + 1 : ℕ) : ℤ) ≫
          eqToHom (congrArg (laurent L).piece hc) :=
  tensorPieceIso_inv_comp_app_add_two (TA T L) (tensorToLaurent L (TA T L))
    (tensorGenerator_comp_tensorToLaurent L (TA T L)) m hc

end Successor

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
