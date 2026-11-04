module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridgeSteps
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransport
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback

/-!
# The bridge, and the bundle of Tag 01O4 at its canonical datum

`Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridge` asks that, in every degree, the
comparison `pullbackTensorPowerIso` of the `m`-fold tensor powers agree, through
`tensorPowerToLaurent`, with the comparison `laurentPullback` of the integral tensor powers of
Tag 01CU. This file proves it, by the induction on `m` whose two base cases are
`tensorPowerToLaurent_zero` in degree zero and
`Stacks.AlgebraicGeometry.ProjRepresentsF1.laurentGenerator_pullback` in degree one, and whose
left-handed successor law for `tensorPowerToLaurent` is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorPowerToLaurent_add_two`; and then, through the
reduction `bundleOfPowerBridge`, it builds the bundle of representing bijections of
Tag 01O4 at the canonical comparison `tensorAlgebraPullbackIsos`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.f1Bundle`: **the bundle of Tag 01O4 at the canonical
  pullback comparison on tensor algebras**, for a quasi-coherent graded algebra generated in
  degree one.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorPowerBridge`: **the bridge.**
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorPieceIso_zero_inv`: **the degree-zero
  identification of a tensor algebra is inverse to its graded unit**, over an arbitrary site:
  the morphism form of the sectionwise field
  `SheafOfModules.TensorExteriorSymmetricAlgebras.tensorPieceIso_zero`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorPowerToLaurent_zero`: **in degree zero the
  comparison of the tensor powers with the Laurent algebra is the identity**, the previous result
  together with `...RelativeProjQcohSheaf.oneHom_comp_app_zero` and
  `...RelativeProjQcohSheaf.oneHom_laurent`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorPowerIso_zero_hom` and
  `...ProjRepresentsF1.pullbackTensorPowerIso_hom_add_two`: the two values of
  `pullbackTensorPowerIso` the induction reads, in degree zero and in degree `m + 2`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso_naturality`: **Tag 01CD at
  the scheme spelling is natural in both module arguments.**
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.bridge_zero` and `...ProjRepresentsF1.bridge_one`:
  the two base cases of the induction.
* `...ProjRepresentsF1.pullbackTensorPowerIso_comp_tensorPowerToLaurent_add_two` and
  `...ProjRepresentsF1.map_tensorPowerToLaurent_comp_laurentPullback_add_two`: **the successor
  laws for the two sides of the bridge**, both at the same presentation of the degree-`(m+2)`
  tensor power as the pullback comparison of Tag 01CD followed by the Laurent generator in the
  left factor and the degree-`(m+1)` datum in the right.

## Implementation notes

The two successor laws are given a common right-hand side: each side of the bridge, read in
degree `m + 2`, becomes the comparison of Tag 01CD followed by one and the same operation applied
to that side in degree `m + 1`. `rec_two` is then the two-step recursion on `ℕ` with nothing in
it but `congrArg`.

The crossing between `Stacks.SheafOfModules.Tensor.sheafTensor`'s functorial action and the
monoidal `⊗ₘ` is paid once, by `...PullbackTensorCoherence.tensorSheaf_map_eq_tensorHom`, inside
the right-hand successor law, where `...RelativeProjQcohSheaf.laurentPullback_mulSheaf` states
the multiplicativity of the comparison of the integral tensor powers with `⊗ₘ`. Everything else
is written at the bifunctor, which needs no monoidal instance.

Each rearrangement is a lemma with every object and morphism free, elaborated once in an abstract
category; the morphisms it is applied to carry the two spellings of the pullback functor
(`AlgebraicGeometry.Scheme.Modules.pullback` against `Stacks.RingedSpace.pullbackFunctor` of the
underlying morphism of ringed spaces) and the two spellings of the comparison of Tag 01CD.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RingedSpace

universe v u w

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

/-! ### Degree zero of a tensor algebra, over an arbitrary site -/

section Abstract

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {F : SheafOfModules.{w} (Sheaf.toRingCat J Osharp)}

/-- **The degree-zero identification of a tensor algebra is inverse to its graded unit.** The
sectionwise field `tensorPieceIso_zero` says that the identification takes the algebra unit to
`1`; the two are the same statement read through the bijection `(𝟙_ ⟶ M) ≃ Γ(M)` of
`SheafOfModules.unitHomEquiv`. -/
public theorem tensorPieceIso_zero_inv
    (B : SheafOfModules.TensorExteriorSymmetricAlgebras J F) :
    B.tensorPieceZeroIsoUnit.inv = SheafOfModules.GradedAlgebra.oneHom B.tensor :=
  (SheafOfModules.unitHomEquiv (B.tensor.piece 0)).injective
    (Eq.trans
      (PresheafOfModules.sections_ext _ _ fun U =>
        Eq.trans
          (congrArg (fun y => B.tensorPieceZeroIsoUnit.inv.val.app U y)
            (B.tensorPieceIso_zero U).symm)
          (Stacks.SheafOfModules.inv_val_app_hom_val_app B.tensorPieceZeroIsoUnit U
            (B.tensor.one.eval U)))
      (SheafOfModules.GradedAlgebra.unitHomEquiv_oneHom B.tensor).symm)

end Abstract

/-! ### Two values of `pullbackTensorPowerIso`, and naturality of Tag 01CD -/

section Values

variable {T T' : Scheme.{u}} (g : T' ⟶ T) (L : T.Modules)

/-- **In degree zero the comparison of the tensor powers is the structure-sheaf comparison of
Tag 01CD**, in the spelling `...PullbackTensorCoherence.pullbackUnitComparison` that
`...RelativeProjQcohSheaf.laurentPullback_zero` is stated with. The zeroth tensor power is the
structure sheaf, `pullbackTensorPowerIso` is `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`
there, and that is `Stacks.PullbackAlgebra.unitComparison` by `rfl`. -/
public theorem pullbackTensorPowerIso_zero_hom :
    (pullbackTensorPowerIso g L 0).hom =
      Stacks.PullbackTensorCoherence.pullbackUnitComparison (ringedSpaceHom g) := rfl

/-- **The successor law for the comparison of the tensor powers.** The `(m+2)`-fold tensor power
is the module tensored with the `(m+1)`-fold one, and under that presentation the comparison in
degree `m + 2` is the comparison of Tag 01CD followed by the comparison in degree `m + 1` in the
second tensor factor. This is the recursion of `pullbackTensorPowerIso`. -/
public theorem pullbackTensorPowerIso_hom_add_two (m : ℕ) :
    (pullbackTensorPowerIso g L (m + 2)).hom =
      (pullbackTensorSchemeIso g L
            (SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) L (m + 1))).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).obj
          ((Scheme.Modules.pullback g).obj L)).map
            ((pullbackTensorPowerIso g L (m + 1)).hom) := rfl

/-- **Tag 01CD at the scheme spelling is natural in both module arguments.** The comparison of
the pullback of a tensor product with the tensor product of the pullbacks is a morphism of
bifunctors; `pullbackTensorSchemeIso` is one component of the isomorphism of bifunctors
`Stacks.PullbackTensorIso.pullbackTensorIso`, so this is that isomorphism's naturality. -/
public theorem pullbackTensorSchemeIso_naturality {M M' N N' : T.Modules} (a : M ⟶ M')
    (b : N ⟶ N') :
    (Scheme.Modules.pullback g).map
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T).sheaf).map a).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T).sheaf).obj _).map b)) ≫
        (pullbackTensorSchemeIso g M' N').hom =
      (pullbackTensorSchemeIso g M N).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).map
          ((Scheme.Modules.pullback g).map a)).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).obj _).map
        ((Scheme.Modules.pullback g).map b)) :=
  (Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.naturality
    ((⟨a, b⟩ : ((M, N) : T.Modules × T.Modules) ⟶ (M', N')))

end Values

/-! ### The rearrangements, with every object and morphism free -/

/-- Merging the two inner factors of a composite of four. -/
private theorem comp_four_merge {D : Type*} [Category D] {W X Y Z R : D} (p : W ⟶ X) {a : X ⟶ Y}
    {b : Y ⟶ Z} (c : Z ⟶ R) {d : X ⟶ Z} (h : a ≫ b = d) :
    (p ≫ a) ≫ b ≫ c = p ≫ d ≫ c := by
  rw [Category.assoc, ← Category.assoc a, h]

/-- **Naturality of a bifunctor in its first variable, merged with functoriality in its
second**: what the left-handed successor law needs of the tensor product. -/
private theorem bifunctor_naturality_merge {D E K : Type*} [Category D] [Category E] [Category K]
    (G : D ⥤ E ⥤ K) {X Y : D} {c : X ⟶ Y} {P Q R : E} {b : P ⟶ Q} {q : Q ⟶ R} :
    (G.obj X).map b ≫ ((G.map c).app Q ≫ (G.obj Y).map q) =
      (G.map c).app P ≫ (G.obj Y).map (b ≫ q) := by
  rw [← Category.assoc, (G.map c).naturality b, Category.assoc, ← (G.obj Y).map_comp]

/-- **The composition law of a bifunctor, written out through its two components**: what the
right-handed successor law needs of the tensor product. -/
private theorem bifunctor_comp {D E K : Type*} [Category D] [Category E] [Category K]
    (G : D ⥤ E ⥤ K) {X Y Z : D} {P Q R : E} (a : X ⟶ Y) (b : P ⟶ Q) (p : Y ⟶ Z) (q : Q ⟶ R) :
    ((G.map a).app P ≫ (G.obj Y).map b) ≫ ((G.map p).app Q ≫ (G.obj Z).map q) =
      (G.map (a ≫ p)).app P ≫ (G.obj Z).map (b ≫ q) :=
  calc ((G.map a).app P ≫ (G.obj Y).map b) ≫ ((G.map p).app Q ≫ (G.obj Z).map q)
      = (G.map a).app P ≫ ((G.obj Y).map b ≫ (G.map p).app Q) ≫ (G.obj Z).map q := by
        simp only [Category.assoc]
    _ = (G.map a).app P ≫ ((G.map p).app P ≫ (G.obj Z).map b) ≫ (G.obj Z).map q := by
        rw [(G.map p).naturality b]
    _ = ((G.map a).app P ≫ (G.map p).app P) ≫ ((G.obj Z).map b ≫ (G.obj Z).map q) := by
        simp only [Category.assoc]
    _ = (G.map (a ≫ p)).app P ≫ (G.obj Z).map (b ≫ q) := by
        rw [← NatTrans.comp_app, ← G.map_comp, ← (G.obj Z).map_comp]

/-- **The rearrangement the right-hand successor law is, with every object and morphism free**:
four commuting squares composed into one. -/
private theorem theta_rearrange {D : Type*} [Category D] {W X Y Z R V₀ V₁ : D}
    {x : W ⟶ X} {lpb : X ⟶ R} {u : W ⟶ Y} {v : Y ⟶ X} {P : Y ⟶ Z} {w : Z ⟶ V₀}
    {z : V₀ ⟶ R} {Q : W ⟶ V₁} {u' : V₁ ⟶ Z} {d : V₁ ⟶ V₀}
    (hstep : x = u ≫ v) (hmul : P ≫ w ≫ z = v ≫ lpb) (hnat : u ≫ P = Q ≫ u')
    (hmerge : u' ≫ w = d) : x ≫ lpb = Q ≫ d ≫ z := by
  calc x ≫ lpb = (u ≫ v) ≫ lpb := by rw [hstep]
    _ = u ≫ v ≫ lpb := by simp only [Category.assoc]
    _ = u ≫ P ≫ w ≫ z := by rw [hmul]
    _ = (u ≫ P) ≫ w ≫ z := by simp only [Category.assoc]
    _ = (Q ≫ u') ≫ w ≫ z := by rw [hnat]
    _ = Q ≫ (u' ≫ w) ≫ z := by simp only [Category.assoc]
    _ = Q ≫ d ≫ z := by rw [hmerge]

/-- **Two families of morphisms with the same two initial values and the same two-step recursion
agree.** -/
private theorem rec_two {D : Type*} [Category D] {X Y : ℕ → D} (Phi Theta : ∀ n, X n ⟶ Y n)
    (F : ∀ m : ℕ, (X (m + 1) ⟶ Y (m + 1)) → (X (m + 2) ⟶ Y (m + 2)))
    (h0 : Phi 0 = Theta 0) (h1 : Phi 1 = Theta 1)
    (hP : ∀ m, Phi (m + 2) = F m (Phi (m + 1)))
    (hT : ∀ m, Theta (m + 2) = F m (Theta (m + 1))) : ∀ n, Phi n = Theta n
  | 0 => h0
  | 1 => h1
  | (m + 2) =>
      (hP m).trans
        ((congrArg (F m) (rec_two Phi Theta F h0 h1 hP hT (m + 1))).trans (hT m).symm)

/-- The degrees of the left-handed successor law add up. -/
private theorem one_add_succ_cast (m : ℕ) :
    (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ) := by push_cast; ring

/-! ### The bridge -/

section Bridge

variable {T T' : Scheme.{u}} (g : T' ⟶ T) (TA : TensorAlgebras.{u}) (L : T.Modules)
  [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]

/-- **In degree zero the comparison of the tensor powers with the Laurent algebra is the
identity.** The degree-zero identification of the tensor algebra is inverse to its graded unit
(`tensorPieceIso_zero_inv`), a unital homomorphism of graded algebras carries the graded unit to
the graded unit (`...RelativeProjQcohSheaf.oneHom_comp_app_zero`), and the graded unit of the
Laurent algebra of an invertible module is the identity of the structure sheaf
(`...RelativeProjQcohSheaf.oneHom_laurent`). -/
public theorem tensorPowerToLaurent_zero :
    tensorPowerToLaurent TA L 0 =
      𝟙 (SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) L 0) :=
  Eq.trans
    (congrArg (fun z => z ≫ (tensorToLaurent L (TA T L)).app 0)
      (tensorPieceIso_zero_inv (TA T L)))
    (Eq.trans
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.oneHom_comp_app_zero
        (tensorToLaurent L (TA T L)))
      (oneHom_laurent L))

/-- **The degree-zero case of the bridge.** Both comparisons of the tensor powers are the
identity in degree zero (`tensorPowerToLaurent_zero`), so what is asked is that the two
structure-sheaf comparisons agree — and they are the same morphism, by
`pullbackTensorPowerIso_zero_hom` and
`...RelativeProjQcohSheaf.laurentPullback_zero`. -/
public theorem bridge_zero :
    (pullbackTensorPowerIso g L 0).hom ≫
        tensorPowerToLaurent TA ((Scheme.Modules.pullback g).obj L) 0 =
      (Scheme.Modules.pullback g).map (tensorPowerToLaurent TA L 0) ≫
        laurentPullback g L ((0 : ℕ) : ℤ) :=
  Eq.trans
    (congrArg (fun z => (pullbackTensorPowerIso g L 0).hom ≫ z)
      (tensorPowerToLaurent_zero TA ((Scheme.Modules.pullback g).obj L)))
    (Eq.trans (Category.comp_id _)
      (Eq.symm (Eq.trans
        (congrArg (fun z => z ≫ laurentPullback g L ((0 : ℕ) : ℤ))
          (Eq.trans (congrArg (Scheme.Modules.pullback g).map (tensorPowerToLaurent_zero TA L))
            ((Scheme.Modules.pullback g).map_id _)))
        (Eq.trans (Category.id_comp (laurentPullback g L ((0 : ℕ) : ℤ)))
          (Eq.trans (laurentPullback_zero g L)
            (pullbackTensorPowerIso_zero_hom g L).symm)))))

/-- **The degree-one case of the bridge.** The comparison of the tensor powers is the identity in
degree one and the comparison with the Laurent algebra is the Laurent generator there
(`tensorPowerToLaurent_one`), so what is asked is that the Laurent generator commute with
pullback, which is `laurentGenerator_pullback`. -/
public theorem bridge_one :
    (pullbackTensorPowerIso g L 1).hom ≫
        tensorPowerToLaurent TA ((Scheme.Modules.pullback g).obj L) 1 =
      (Scheme.Modules.pullback g).map (tensorPowerToLaurent TA L 1) ≫
        laurentPullback g L ((1 : ℕ) : ℤ) :=
  Eq.trans
    (congrArg (fun z => (pullbackTensorPowerIso g L 1).hom ≫ z)
      (tensorPowerToLaurent_one TA ((Scheme.Modules.pullback g).obj L)))
    (Eq.trans (Category.id_comp (laurentGenerator ((Scheme.Modules.pullback g).obj L)))
      (Eq.trans (laurentGenerator_pullback g L)
        (congrArg (fun z => (Scheme.Modules.pullback g).map z ≫ laurentPullback g L ((1 : ℕ) : ℤ))
          (tensorPowerToLaurent_one TA L).symm)))

/-- **The successor law for the left-hand side of the bridge.** The comparison of the tensor
powers in degree `m + 2`, followed by the comparison with the Laurent algebra of the pullback, is
the comparison of Tag 01CD followed by the Laurent generator of the pullback in the left tensor
factor and the left-hand side in degree `m + 1` in the right, and then the multiplication of the
Laurent algebra in bidegree `(1, m+1)`.

This is `pullbackTensorPowerIso_hom_add_two` and `tensorPowerToLaurent_add_two`, the second
factor of the first merging into the left factor of the second. -/
public theorem pullbackTensorPowerIso_comp_tensorPowerToLaurent_add_two (m : ℕ)
    (hc : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ)) :
    (pullbackTensorPowerIso g L (m + 2)).hom ≫
        tensorPowerToLaurent TA ((Scheme.Modules.pullback g).obj L) (m + 2) =
      (pullbackTensorSchemeIso g L
            (SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) L (m + 1))).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).map
          (laurentGenerator ((Scheme.Modules.pullback g).obj L))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).obj _).map
        ((pullbackTensorPowerIso g L (m + 1)).hom ≫
                tensorPowerToLaurent TA ((Scheme.Modules.pullback g).obj L) (m + 1))) ≫
          (laurent ((Scheme.Modules.pullback g).obj L)).mulSheaf 1 ((m + 1 : ℕ) : ℤ) ≫
            eqToHom (congrArg (laurent ((Scheme.Modules.pullback g).obj L)).piece hc) := by
  rw [pullbackTensorPowerIso_hom_add_two,
    tensorPowerToLaurent_add_two TA ((Scheme.Modules.pullback g).obj L) m hc]
  exact comp_four_merge _ _
    (bifunctor_naturality_merge
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf))

/-- **The successor law for the right-hand side of the bridge**, at the same presentation of the
degree-`(m+2)` tensor power as the left-hand one.

Four facts compose into it: `tensorPowerToLaurent_add_two` under the pullback functor;
`...RelativeProjQcohSheaf.laurentPullback_mulSheaf` in bidegree `(1, m+1)`, which is where the
comparison of Tag 01CD enters; `pullbackTensorSchemeIso_naturality`, which moves that comparison
past the pullback of the degree-`(m+2)` datum; and `laurentGenerator_pullback` in the left tensor
factor. -/
public theorem map_tensorPowerToLaurent_comp_laurentPullback_add_two (m : ℕ)
    (hc : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ)) :
    (Scheme.Modules.pullback g).map (tensorPowerToLaurent TA L (m + 2)) ≫
        laurentPullback g L ((m + 2 : ℕ) : ℤ) =
      (pullbackTensorSchemeIso g L
            (SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) L (m + 1))).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).map
          (laurentGenerator ((Scheme.Modules.pullback g).obj L))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).obj _).map
        ((Scheme.Modules.pullback g).map (tensorPowerToLaurent TA L (m + 1)) ≫
                laurentPullback g L ((m + 1 : ℕ) : ℤ))) ≫
          (laurent ((Scheme.Modules.pullback g).obj L)).mulSheaf 1 ((m + 1 : ℕ) : ℤ) ≫
            eqToHom (congrArg (laurent ((Scheme.Modules.pullback g).obj L)).piece hc) :=
  theta_rearrange
    (Eq.trans
      (congrArg (Scheme.Modules.pullback g).map (tensorPowerToLaurent_add_two TA L m hc))
      ((Scheme.Modules.pullback g).map_comp _ _))
    (laurentPullback_mulSheaf L g 1 ((m + 1 : ℕ) : ℤ) ((m + 2 : ℕ) : ℤ) hc)
    (pullbackTensorSchemeIso_naturality g (laurentGenerator L)
      (tensorPowerToLaurent TA L (m + 1)))
    (Eq.trans
      (congrArg (fun z =>
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).map
          ((Scheme.Modules.pullback g).map (laurentGenerator L))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).obj _).map
        ((Scheme.Modules.pullback g).map (tensorPowerToLaurent TA L (m + 1)))) ≫ z)
        (Stacks.PullbackTensorCoherence.tensorSheaf_map_eq_tensorHom
          (laurentPullback g L 1) (laurentPullback g L ((m + 1 : ℕ) : ℤ))).symm)
      (by
        rw [laurentGenerator_pullback g L]
        exact bifunctor_comp (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf)
          ((Scheme.Modules.pullback g).map (laurentGenerator L))
          ((Scheme.Modules.pullback g).map (tensorPowerToLaurent TA L (m + 1)))
          (laurentPullback g L 1) (laurentPullback g L ((m + 1 : ℕ) : ℤ))))

/-- **The bridge.** In every degree the comparison `pullbackTensorPowerIso` of the tensor powers
agrees, through `tensorPowerToLaurent`, with the comparison `laurentPullback` of the integral
tensor powers of Tag 01CU.

The induction is `rec_two` on the two base cases `bridge_zero` and `bridge_one` and the two
successor laws, which present the two sides in degree `m + 2` by the same operation applied to
them in degree `m + 1`. -/
public theorem tensorPowerBridge : TensorPowerBridge TA g L :=
  rec_two
    (fun m => (pullbackTensorPowerIso g L m).hom ≫
      tensorPowerToLaurent TA ((Scheme.Modules.pullback g).obj L) m)
    (fun m => (Scheme.Modules.pullback g).map (tensorPowerToLaurent TA L m) ≫
      laurentPullback g L (m : ℤ))
    (fun m psi =>
      (pullbackTensorSchemeIso g L
            (SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) L (m + 1))).hom ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).map
          (laurentGenerator ((Scheme.Modules.pullback g).obj L))).app _ ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (T').sheaf).obj _).map psi) ≫
          (laurent ((Scheme.Modules.pullback g).obj L)).mulSheaf 1 ((m + 1 : ℕ) : ℤ) ≫
            eqToHom (congrArg (laurent ((Scheme.Modules.pullback g).obj L)).piece
              (one_add_succ_cast m)))
    (bridge_zero g TA L) (bridge_one g TA L)
    (fun m => pullbackTensorPowerIso_comp_tensorPowerToLaurent_add_two g TA L m
      (one_add_succ_cast m))
    (fun m => map_tensorPowerToLaurent_comp_laurentPullback_add_two g TA L m
      (one_add_succ_cast m))

end Bridge

/-! ### The bundle -/

/-- **The bundle of representing bijections of Tag 01O4, at the canonical comparison
`tensorAlgebraPullbackIsos` of the pullback of a tensor algebra.** For a quasi-coherent graded
algebra generated in degree one, the morphisms from a test scheme to its relative homogeneous
spectrum over the base correspond to the strict isomorphism classes of invertible degree-one
quotients of its pullback, naturally in the test scheme and normalised at the identity.

This is the reduction `bundleOfPowerBridge` at `tensorPowerBridge`. -/
public def f1Bundle {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})
    (hgen : IsGeneratedInDegreeOne A) : F1Bundle A TA (tensorAlgebraPullbackIsos TA) :=
  bundleOfPowerBridge A TA hgen fun g L hL => letI := hL; tensorPowerBridge g TA L

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
