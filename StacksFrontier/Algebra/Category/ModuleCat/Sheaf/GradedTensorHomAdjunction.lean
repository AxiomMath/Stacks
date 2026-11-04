module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedTensorProduct

/-!
# Tensor-hom adjunction for sheaves of graded modules

Let `R` be a sheaf of rings on a site `(C, J)`, let `A` and `B` be sheaves of graded
`R`-algebras, let `M` be a right graded `A`-module, let `N` be a graded `(A, B)`-bimodule and
let `L` be a right graded `B`-module. Writing `T` for the tensor product `M ⊗_A N`, a right
graded `B`-module, and `H` for the internal hom `SheafHom^gr_B(N, L)`, a right graded
`A`-module, the two displayed identities of the tensor-hom adjunction hold:

`Hom_{Mod^gr(B)}(M ⊗_A N, L) = Hom_{Mod^gr(A)}(M, SheafHom^gr_B(N, L))`

and

`SheafHom^gr_B(M ⊗_A N, L) = SheafHom^gr_A(M, SheafHom^gr_B(N, L))`.

Both come from reading each side as the `A`-balanced graded bilinear maps `M × N → L` which are
`B`-linear on the right.

## Main definitions

* `SheafOfModules.balancedEquiv` identifies the degree-`n` local homomorphisms
  `M|_U → SheafHom^gr_B(N, L)|_U` of right graded `A`-modules with the `A`-balanced bilinear
  families of degree `n` over `U`. `SheafOfModules.toBalanced` and `SheafOfModules.ofBalanced`
  are its two directions, `SheafOfModules.balancedVal` the value of the family attached to a
  local homomorphism, and `SheafOfModules.balancedHom` the local homomorphism `N|_V → L|_V`
  that a balanced bilinear family attaches to a local section of `M`.

## Main results

* `SheafOfModules.tensorHomEquiv` is the first displayed identity: the degree-`n` homomorphisms
  `M ⊗_A N → L` of right graded `B`-modules are the degree-`n` homomorphisms
  `M → SheafHom^gr_B(N, L)` of right graded `A`-modules.
* `SheafOfModules.isGradedSheafHom_tensor` is the second: a graded sheaf of `R`-modules which is
  the internal hom `SheafHom^gr_B(M ⊗_A N, L)` is also the internal hom
  `SheafHom^gr_A(M, SheafHom^gr_B(N, L))`.
* `SheafOfModules.toBalanced_restrict` and `SheafOfModules.ofBalanced_restrict`: the local
  identification is compatible with restriction along a morphism of the site.

## Implementation notes

Neither the tensor product nor the internal hom can be written down by a formula over a general
ringed site, so both are used through the predicates `SheafOfModules.IsGradedTensorProduct` and
`SheafOfModules.IsGradedInternalHom`, which pin them up to canonical isomorphism; see the
implementation notes of the two files where those are defined. Accordingly both identities are
stated for an arbitrary `T` which *is* `M ⊗_A N` and an arbitrary `H` which *is*
`SheafHom^gr_B(N, L)`.

The second identity is stated as a transfer of the predicate rather than as an isomorphism of
graded sheaves: a graded sheaf of `R`-modules which is the one internal hom is also the other.
That is the content of the source's equality of two internal homs, and it avoids choosing one of
the two as a representative.

The first identity is deduced from the local one, not proved separately: a homogeneous
homomorphism of degree `n` is the same datum as a family of degree-`n` local homomorphisms, one
over each object of the site, compatible with restriction
(`SheafOfModules.GradedHomOfDegree.ofLocal` and `toLocal`), and both the universal property of
the tensor product and the local identification are compatible with restriction.

A balanced bilinear family takes its second argument in `N^j`, while a local homomorphism out of
the bimodule takes it in `(N.toGradedModule)^j`. These are the same type, but not the same
expression, so the rewriting lemmas below are stated as equalities of the additive maps rather
than of their values, and the bridges between the two spellings are `rfl` lemmas stated where
they are used.

`M` and `H` are taken in one module universe because a homogeneous homomorphism between them is
a family of morphisms of sheaves of modules; likewise `T` and `L`, which the universal property
of the tensor product already forces. The base is an arbitrary sheaf of rings on an arbitrary
site rather than the structure sheaf of a ringed site; a ringed site `X` is the case
`R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FR6](https://stacks.math.columbia.edu/tag/0FR6)
* [Stacks Project, Tag 0FR4](https://stacks.math.columbia.edu/tag/0FR4)
-/

@[expose] public section

open CategoryTheory

universe t a w z s g v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : GradedAlgebra.{t, a} R} {M H : GradedModule.{t, a, w} A}
  {N : GradedBimodule.{t, a, z} A B} {L T : GradedModule.{t, a, s} B} {n : ℤ}

/-- Restricting a local section of the sheaf of rings along a composite is restricting it
twice. -/
theorem ring_map_comp_op {X Y Z : C} (f : Z ⟶ Y) (q : Y ⟶ X)
    (r : R.obj.obj (Opposite.op X)) :
    R.obj.map (f ≫ q).op r = R.obj.map f.op (R.obj.map q.op r) := by
  rw [op_comp, R.obj.map_comp]
  rfl

/-! ### From a local homomorphism into the internal hom to a balanced bilinear family -/

/-- The value on a local section of `M^i` of the `A`-balanced bilinear family attached to a
degree-`n` local homomorphism `M|_U → SheafHom^gr_B(N, L)|_U`: it sends `(x, y)` to the value
at `y` of the local homomorphism `f (x)`. -/
noncomputable def balancedVal (hH : IsGradedInternalHom N L H) {U : C}
    (f : GradedLocalHom M H n U) (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k)
    (V : Over U) (x : (M.piece i).val.obj (Opposite.op V.left)) :
    (N.piece j).val.obj (Opposite.op V.left) →+ (L.piece k).val.obj (Opposite.op V.left) :=
  (hH.sectionsEquiv m V.left (f.app i m him V x)).app j k hjk (Over.mk (𝟙 V.left))

/-- The value of `balancedVal hH f` on `x` is the value at the identity of `V.left` of the local
homomorphism `N|_{V.left} → L|_{V.left}` corresponding to the section `f (x)` of the internal
hom. -/
theorem balancedVal_eq (hH : IsGradedInternalHom N L H) {U : C} (f : GradedLocalHom M H n U)
    (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k) (V : Over U)
    (x : (M.piece i).val.obj (Opposite.op V.left)) :
    balancedVal hH f i j k m him hjk V x =
      (hH.sectionsEquiv m V.left (f.app i m him V x)).app j k hjk
        (Over.mk (𝟙 V.left)) := rfl

/-- The intermediate degree in the value of a balanced bilinear family is determined by the
other two, so any proof of its defining equation gives the same value. -/
theorem balancedVal_congr (hH : IsGradedInternalHom N L H) {U : C}
    (f : GradedLocalHom M H n U) (i j k m m' : ℤ) (him : i + n = m) (him' : i + n = m')
    (hjk : j + m = k) (hjk' : j + m' = k) (V : Over U)
    (x : (M.piece i).val.obj (Opposite.op V.left))
    (y : (N.piece j).val.obj (Opposite.op V.left)) :
    balancedVal hH f i j k m him hjk V x y = balancedVal hH f i j k m' him' hjk' V x y := by
  obtain rfl : m = m' := by omega
  rfl

/-- The family `balancedVal hH f` is additive in its first argument. -/
theorem balancedVal_add (hH : IsGradedInternalHom N L H) {U : C}
    (f : GradedLocalHom M H n U) (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k)
    (V : Over U) (x x' : (M.piece i).val.obj (Opposite.op V.left))
    (y : (N.piece j).val.obj (Opposite.op V.left)) :
    balancedVal hH f i j k m him hjk V (x + x') y =
      balancedVal hH f i j k m him hjk V x y + balancedVal hH f i j k m him hjk V x' y := by
  rw [balancedVal_eq, balancedVal_eq, balancedVal_eq,
    show f.app i m him V (x + x') = f.app i m him V x + f.app i m him V x' from map_add _ _ _]
  exact hH.sectionsEquiv_add m V.left _ _ j k hjk (Over.mk (𝟙 V.left)) y

/-- The family `balancedVal hH f` is `R`-linear in its first argument. -/
theorem balancedVal_smul (hH : IsGradedInternalHom N L H) {U : C}
    (f : GradedLocalHom M H n U) (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k)
    (V : Over U) (r : R.obj.obj (Opposite.op V.left))
    (x : (M.piece i).val.obj (Opposite.op V.left))
    (y : (N.piece j).val.obj (Opposite.op V.left)) :
    balancedVal hH f i j k m him hjk V (r • x) y =
      r • balancedVal hH f i j k m him hjk V x y := by
  rw [balancedVal_eq, balancedVal_eq,
    show f.app i m him V (r • x) = r • f.app i m him V x from f.map_smul i m him V r x]
  exact hH.sectionsEquiv_smul_top m V.left r _ j k hjk y

/-- The family `balancedVal hH f` commutes with restriction along a morphism `W ⟶ V` over
`U`. -/
theorem balancedVal_naturality (hH : IsGradedInternalHom N L H) {U : C}
    (f : GradedLocalHom M H n U) (i j k m : ℤ) (him : i + n = m) (hjk : j + m = k)
    {V W : Over U} (q : W ⟶ V) (x : (M.piece i).val.obj (Opposite.op V.left))
    (y : (N.piece j).val.obj (Opposite.op V.left)) :
    (L.piece k).val.map q.left.op (balancedVal hH f i j k m him hjk V x y) =
      balancedVal hH f i j k m him hjk W ((M.piece i).val.map q.left.op x)
        ((N.piece j).val.map q.left.op y) := by
  have hW : balancedVal hH f i j k m him hjk W ((M.piece i).val.map q.left.op x) =
      (hH.sectionsEquiv m W.left
        (f.app i m him W ((M.piece i).val.map q.left.op x))).app j k hjk
        (Over.mk (𝟙 W.left)) := rfl
  rw [balancedVal_eq, hW]
  refine ((hH.sectionsEquiv m V.left (f.app i m him V x)).naturality j k hjk
    (Over.homMk q.left (Category.comp_id q.left) :
      Over.mk q.left ⟶ Over.mk (𝟙 V.left)) y).trans ?_
  refine ((hH.sectionsEquiv m V.left (f.app i m him V x)).app_mk_congr j k hjk
    (Category.id_comp q.left).symm _).trans ?_
  refine (DFunLike.congr_fun (hH.sectionsEquiv_naturality m q.left (f.app i m him V x) j k hjk
    (Over.mk (𝟙 W.left))) ((N.piece j).val.map q.left.op y)).symm.trans ?_
  exact congrArg (fun pp : (H.piece m).val.obj (Opposite.op W.left) =>
    (hH.sectionsEquiv m W.left pp).app j k hjk (Over.mk (𝟙 W.left))
      ((N.piece j).val.map q.left.op y)) (f.naturality i m him q x)

/-- The `A`-balanced bilinear family of degree `n` attached to a degree-`n` local homomorphism
`M|_U → SheafHom^gr_B(N, L)|_U` of right graded `A`-modules. -/
noncomputable def toBalanced (hH : IsGradedInternalHom N L H) {U : C}
    (f : GradedLocalHom M H n U) : GradedLocalBalanced M N L n U where
  app i j k hijk V := AddMonoidHom.mk'
    (fun x => balancedVal hH f i j k (i + n) rfl (by omega) V x)
    (fun x x' => AddMonoidHom.ext fun y =>
      balancedVal_add hH f i j k (i + n) rfl (by omega) V x x' y)
  map_smul_left i j k hijk V r x y :=
    balancedVal_smul hH f i j k (i + n) rfl (by omega) V r x y
  map_smul_right i j k hijk V r x y :=
    (hH.sectionsEquiv (i + n) V.left (f.app i (i + n) rfl V x)).map_smul j k (by omega)
      (Over.mk (𝟙 V.left)) r y
  naturality i j k hijk {V W} q x y :=
    balancedVal_naturality hH f i j k (i + n) rfl (by omega) q x y
  balanced i p j k hijk V x b y := by
    refine (balancedVal_congr hH f (i + p) j k (i + p + n) (i + n + p) rfl (by omega)
      (by omega) (by omega) V _ y).trans ?_
    refine Eq.trans ?_ (hH.sectionsEquiv_mul_top (i + n) p V.left (f.app i (i + n) rfl V x) b
      j k (by omega) y)
    exact congrArg (fun pp : (H.piece (i + n + p)).val.obj (Opposite.op V.left) =>
      (hH.sectionsEquiv (i + n + p) V.left pp).app j k (by omega) (Over.mk (𝟙 V.left)) y)
      (f.map_mul i (i + n) rfl p V x b)
  map_rightMul i j p k hijk V x y b :=
    (hH.sectionsEquiv (i + n) V.left (f.app i (i + n) rfl V x)).map_mul j k (by omega) p
      (Over.mk (𝟙 V.left)) y b

/-- The component of `toBalanced hH f` in degrees `i`, `j`, `k` is `balancedVal hH f` with
intermediate degree `i + n`. -/
theorem toBalanced_app (hH : IsGradedInternalHom N L H) {U : C} (f : GradedLocalHom M H n U)
    (i j k : ℤ) (hijk : i + j + n = k) (V : Over U)
    (x : (M.piece i).val.obj (Opposite.op V.left)) :
    (toBalanced hH f).app i j k hijk V x =
      balancedVal hH f i j k (i + n) rfl (by omega) V x := rfl

/-! ### From a balanced bilinear family to a local homomorphism into the internal hom -/

/-- The local homomorphism `N|_{V.left} → L|_{V.left}` of right graded `B`-modules of degree `j`
that an `A`-balanced bilinear family of degree `n` attaches to a local section `x` of `M^i`,
where `i + n = j`. It sends `y` to the value of the family on `(x, y)`. -/
noncomputable def balancedHom {U : C} (β : GradedLocalBalanced M N L n U) {i j : ℤ}
    (hij : i + n = j) (V : Over U) (x : (M.piece i).val.obj (Opposite.op V.left)) :
    GradedLocalHom N.toGradedModule L j V.left where
  app j' k hj'k W := β.app i j' k (by omega) (Over.mk (W.hom ≫ V.hom))
    ((M.piece i).val.map W.hom.op x)
  map_smul j' k hj'k W r y :=
    β.map_smul_right i j' k (by omega) (Over.mk (W.hom ≫ V.hom)) r _ y
  naturality j' k hj'k {W₁ W₂} q y := by
    have hw : q.left ≫ (Over.mk (W₁.hom ≫ V.hom)).hom = (Over.mk (W₂.hom ≫ V.hom)).hom := by
      change q.left ≫ W₁.hom ≫ V.hom = W₂.hom ≫ V.hom
      rw [← Category.assoc, Over.w q]
    have hmx : (M.piece i).val.map q.left.op ((M.piece i).val.map W₁.hom.op x) =
        (M.piece i).val.map W₂.hom.op x := by
      rw [← (M.piece i).val.map_comp_apply, ← op_comp, Over.w q]
    refine (β.naturality i j' k (by omega)
      (Over.homMk q.left hw :
        Over.mk (W₂.hom ≫ V.hom) ⟶ Over.mk (W₁.hom ≫ V.hom)) _ y).trans ?_
    exact congrArg (fun v : (M.piece i).val.obj (Opposite.op W₂.left) =>
      β.app i j' k (by omega) (Over.mk (W₂.hom ≫ V.hom)) v
        ((N.piece j').val.map q.left.op y)) hmx
  map_mul j' k hj'k p W y b :=
    β.map_rightMul i j' p k (by omega) (Over.mk (W.hom ≫ V.hom)) _ y b

/-- The value of `balancedHom β hij V x` over `W` is the value of `β` over `W` on the restriction
of `x` to `W`. -/
theorem balancedHom_eq {U : C} (β : GradedLocalBalanced M N L n U) {i j : ℤ} (hij : i + n = j)
    (V : Over U) (x : (M.piece i).val.obj (Opposite.op V.left)) (j' k : ℤ) (hj'k : j' + j = k)
    (W : Over V.left) :
    (balancedHom β hij V x).app j' k hj'k W =
      β.app i j' k (by omega) (Over.mk (W.hom ≫ V.hom))
        ((M.piece i).val.map W.hom.op x) := rfl

/-- The degree-`n` local homomorphism `M|_U → SheafHom^gr_B(N, L)|_U` of right graded
`A`-modules attached to an `A`-balanced bilinear family of degree `n` over `U`. -/
noncomputable def ofBalanced (hH : IsGradedInternalHom N L H) {U : C}
    (β : GradedLocalBalanced M N L n U) : GradedLocalHom M H n U where
  app i j hij V := AddMonoidHom.mk'
    (fun x => (hH.sectionsEquiv j V.left).symm (balancedHom β hij V x))
    (fun x x' => hH.symm_add j V.left _ _ _ fun j' k hj'k W y => by
      rw [balancedHom_eq, balancedHom_eq, balancedHom_eq,
        show (M.piece i).val.map W.hom.op (x + x') =
            (M.piece i).val.map W.hom.op x + (M.piece i).val.map W.hom.op x' from
          map_add _ _ _]
      exact DFunLike.congr_fun (map_add (β.app i j' k (by omega)
        (Over.mk (W.hom ≫ V.hom))) _ _) y)
  map_smul i j hij V r x :=
    hH.symm_smul j V.left r _ _ fun j' k hj'k W y => by
      rw [balancedHom_eq, balancedHom_eq,
        show (M.piece i).val.map W.hom.op (r • x) =
            R.obj.map W.hom.op r • (M.piece i).val.map W.hom.op x from
          PresheafOfModules.map_smul _ _ _ _]
      exact β.map_smul_left i j' k (by omega) (Over.mk (W.hom ≫ V.hom)) _ _ y
  naturality i j hij {V W} q x := by
    have hres : (balancedHom β hij V x).restrict q.left =
        balancedHom β hij W ((M.piece i).val.map q.left.op x) := by
      refine GradedLocalHom.ext fun j' k hj'k W' y => ?_
      have hov : (W'.hom ≫ q.left) ≫ V.hom = W'.hom ≫ W.hom := by
        rw [Category.assoc, Over.w q]
      have hsec : (M.piece i).val.map (W'.hom ≫ q.left).op x =
          (M.piece i).val.map W'.hom.op ((M.piece i).val.map q.left.op x) := by
        rw [op_comp, (M.piece i).val.map_comp_apply]
      have hl : ((balancedHom β hij V x).restrict q.left).app j' k hj'k W' y =
          β.app i j' k (by omega) (Over.mk ((W'.hom ≫ q.left) ≫ V.hom))
            ((M.piece i).val.map (W'.hom ≫ q.left).op x) y := rfl
      have hr : (balancedHom β hij W ((M.piece i).val.map q.left.op x)).app j' k hj'k W' y =
          β.app i j' k (by omega) (Over.mk (W'.hom ≫ W.hom))
            ((M.piece i).val.map W'.hom.op ((M.piece i).val.map q.left.op x)) y := rfl
      refine hl.trans (Eq.trans ?_ hr.symm)
      refine (β.app_mk_congr i j' k (by omega) hov _ y).trans ?_
      exact congrArg (fun v : (M.piece i).val.obj (Opposite.op W'.left) =>
        β.app i j' k (by omega) (Over.mk (W'.hom ≫ W.hom)) v y) hsec
    exact (hH.symm_naturality j q.left (balancedHom β hij V x)).symm.trans
      (congrArg (hH.sectionsEquiv j W.left).symm hres)
  map_mul i j hij p V x b := by
    change (hH.sectionsEquiv (j + p) V.left).symm
        (balancedHom β (by omega) V (M.smul i p (Opposite.op V.left) x b)) =
      H.smul j p (Opposite.op V.left)
        ((hH.sectionsEquiv j V.left).symm (balancedHom β hij V x)) b
    rw [Equiv.symm_apply_eq, hH.sectionsEquiv_mul, Equiv.apply_symm_apply]
    refine GradedLocalHom.ext fun j' k hj'k W y => ?_
    have hl : (balancedHom β (show i + p + n = j + p by omega) V
            (M.smul i p (Opposite.op V.left) x b)).app j' k hj'k W y =
        β.app (i + p) j' k (by omega) (Over.mk (W.hom ≫ V.hom))
          ((M.piece (i + p)).val.map W.hom.op
            (M.smul i p (Opposite.op V.left) x b)) y := rfl
    have hr : ((balancedHom β hij V x).actRight p b).app j' k hj'k W y =
        β.app i (p + j') k (by omega) (Over.mk (W.hom ≫ V.hom))
          ((M.piece i).val.map W.hom.op x)
          ((N.leftMul p j').app (Opposite.op W.left)
            ((A.piece p).val.map W.hom.op b) y) := rfl
    refine hl.trans (Eq.trans ?_ hr.symm)
    rw [M.smul_naturality i p W.hom.op x b]
    exact β.balanced i p j' k (by omega) (Over.mk (W.hom ≫ V.hom)) _ _ y

/-- The value of `ofBalanced hH β` on `x` is the section of the internal hom corresponding to the
local homomorphism `balancedHom β hij V x`. -/
theorem ofBalanced_app (hH : IsGradedInternalHom N L H) {U : C}
    (β : GradedLocalBalanced M N L n U) (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : (M.piece i).val.obj (Opposite.op V.left)) :
    (ofBalanced hH β).app i j hij V x =
      (hH.sectionsEquiv j V.left).symm (balancedHom β hij V x) := rfl

/-! ### The two constructions are inverse to one another -/

/-- `ofBalanced hH` is a left inverse of `toBalanced hH`. -/
theorem ofBalanced_toBalanced (hH : IsGradedInternalHom N L H) {U : C}
    (f : GradedLocalHom M H n U) : ofBalanced hH (toBalanced hH f) = f := by
  refine GradedLocalHom.ext fun i j hij V x => ?_
  rw [ofBalanced_app, Equiv.symm_apply_eq]
  refine GradedLocalHom.ext fun j' k hj'k W y => ?_
  rw [balancedHom_eq]
  refine (balancedVal_congr hH f i j' k (i + n) j rfl hij (by omega) (by omega)
    (Over.mk (W.hom ≫ V.hom)) _ y).trans ?_
  have key : balancedVal hH f i j' k j hij hj'k (Over.mk (W.hom ≫ V.hom))
        ((M.piece i).val.map W.hom.op x) y =
      (hH.sectionsEquiv j W.left (f.app i j hij (Over.mk (W.hom ≫ V.hom))
        ((M.piece i).val.map W.hom.op x))).app j' k hj'k (Over.mk (𝟙 W.left)) y := rfl
  have hnat : f.app i j hij (Over.mk (W.hom ≫ V.hom)) ((M.piece i).val.map W.hom.op x) =
      (H.piece j).val.map W.hom.op (f.app i j hij V x) :=
    (f.naturality i j hij (Over.homMk W.hom rfl : Over.mk (W.hom ≫ V.hom) ⟶ V) x).symm
  rw [key, hnat,
    hH.sectionsEquiv_naturality j W.hom (f.app i j hij V x) j' k hj'k (Over.mk (𝟙 W.left))]
  exact (hH.sectionsEquiv j V.left (f.app i j hij V x)).app_mk_congr j' k hj'k
    (Category.id_comp W.hom) y

/-- `toBalanced hH` is a left inverse of `ofBalanced hH`. -/
theorem toBalanced_ofBalanced (hH : IsGradedInternalHom N L H) {U : C}
    (β : GradedLocalBalanced M N L n U) : toBalanced hH (ofBalanced hH β) = β := by
  refine GradedLocalBalanced.ext fun i j k hijk V x y => ?_
  have key : (toBalanced hH (ofBalanced hH β)).app i j k hijk V x y =
      (hH.sectionsEquiv (i + n) V.left
        ((hH.sectionsEquiv (i + n) V.left).symm
          (balancedHom β rfl V x))).app j k (by omega) (Over.mk (𝟙 V.left)) y := rfl
  rw [key, Equiv.apply_symm_apply, balancedHom_eq]
  exact β.app_top i j k hijk V x y

/-- The degree-`n` local homomorphisms `M|_U → SheafHom^gr_B(N, L)|_U` of right graded
`A`-modules are the `A`-balanced bilinear families of degree `n` over `U`. This is the local
form of the tensor-hom adjunction. -/
@[stacks 0FR4 "local homomorphisms into the internal hom are balanced bilinear families"]
noncomputable def balancedEquiv (hH : IsGradedInternalHom N L H)
    (M : GradedModule.{t, a, w} A) (n : ℤ) (U : C) :
    GradedLocalHom M H n U ≃ GradedLocalBalanced M N L n U where
  toFun := toBalanced hH
  invFun := ofBalanced hH
  left_inv := ofBalanced_toBalanced hH
  right_inv := toBalanced_ofBalanced hH

/-- `toBalanced hH` commutes with restriction along a morphism `U' ⟶ U` of the site. -/
theorem toBalanced_restrict (hH : IsGradedInternalHom N L H) {U U' : C} (q : U' ⟶ U)
    (f : GradedLocalHom M H n U) :
    (toBalanced hH f).restrict q = toBalanced hH (f.restrict q) := by
  refine GradedLocalBalanced.ext fun i j k hijk V x y => ?_
  rfl

/-- `ofBalanced hH` commutes with restriction along a morphism `U' ⟶ U` of the site. -/
theorem ofBalanced_restrict (hH : IsGradedInternalHom N L H) {U U' : C} (q : U' ⟶ U)
    (β : GradedLocalBalanced M N L n U) :
    (ofBalanced hH β).restrict q = ofBalanced hH (β.restrict q) := by
  have h := toBalanced_restrict hH q (ofBalanced hH β)
  rw [toBalanced_ofBalanced] at h
  rw [h, ofBalanced_toBalanced]

/-! ### The two displayed identities -/

/-- **Tensor-hom adjunction for sheaves of graded modules**, first identity: the degree-`n`
homomorphisms `M ⊗_A N → L` of right graded `B`-modules are the degree-`n` homomorphisms
`M → SheafHom^gr_B(N, L)` of right graded `A`-modules. -/
@[stacks 0FR6 "Hom_{Mod^gr(B)}(M ⊗_A N, L) = Hom_{Mod^gr(A)}(M, SheafHom^gr_B(N, L))"]
noncomputable def tensorHomEquiv (hT : IsGradedTensorProduct M N T)
    (hH : IsGradedInternalHom N L H) (n : ℤ) :
    GradedHomOfDegree T L n ≃ GradedHomOfDegree M H n where
  toFun φ := GradedHomOfDegree.ofLocal
    (fun U => ofBalanced hH (hT.universal L n U (φ.toLocal U)))
    (fun {U U'} q => by
      have h : hT.universal L n U' (φ.toLocal U') =
          (hT.universal L n U (φ.toLocal U)).restrict q := by
        refine GradedLocalBalanced.ext fun i j k hijk V x y => ?_
        rw [GradedLocalBalanced.restrict_app,
          ← hT.universal_restrict L n q (φ.toLocal U) i j k hijk V x y]
        exact congrArg (fun z : GradedLocalHom T L n U' =>
          (hT.universal L n U' z).app i j k hijk V x y)
          (GradedHomOfDegree.restrict_toLocal φ q).symm
      rw [ofBalanced_restrict, h])
  invFun ψ := GradedHomOfDegree.ofLocal
    (fun U => (hT.universal L n U).symm (toBalanced hH (ψ.toLocal U)))
    (fun {U U'} q => by
      rw [hT.universal_symm_restrict, toBalanced_restrict]
      exact congrArg (fun z : GradedLocalHom M H n U' =>
        (hT.universal L n U').symm (toBalanced hH z))
        (GradedHomOfDegree.restrict_toLocal ψ q))
  left_inv φ := GradedHomOfDegree.eq_of_toLocal fun U => by
    rw [GradedHomOfDegree.toLocal_ofLocal, GradedHomOfDegree.toLocal_ofLocal,
      toBalanced_ofBalanced, Equiv.symm_apply_apply]
  right_inv ψ := GradedHomOfDegree.eq_of_toLocal fun U => by
    rw [GradedHomOfDegree.toLocal_ofLocal, GradedHomOfDegree.toLocal_ofLocal,
      Equiv.apply_symm_apply, ofBalanced_toBalanced]

/-- **Tensor-hom adjunction for sheaves of graded modules**, second identity: a graded sheaf of
`R`-modules which is the internal hom `SheafHom^gr_B(M ⊗_A N, L)` is also the internal hom
`SheafHom^gr_A(M, SheafHom^gr_B(N, L))`. -/
@[stacks 0FR6 "SheafHom^gr_B(M ⊗_A N, L) = SheafHom^gr_A(M, SheafHom^gr_B(N, L))"]
noncomputable def isGradedSheafHom_tensor (hT : IsGradedTensorProduct M N T)
    (hH : IsGradedInternalHom N L H) {G : ℤ → SheafOfModules.{g} R}
    (hG : IsGradedSheafHom T L G) : IsGradedSheafHom M H G where
  sectionsEquiv n U := (hG.sectionsEquiv n U).trans
    ((hT.universal L n U).trans (balancedEquiv hH M n U).symm)
  sectionsEquiv_add n U p q i j hij V x := by
    refine hH.symm_add j V.left _ _ _ fun j' k hj'k W y => ?_
    have e : ∀ r : (G n).val.obj (Opposite.op U),
        (balancedHom (hT.universal L n U (hG.sectionsEquiv n U r)) hij V x).app j' k hj'k W y =
          (hG.sectionsEquiv n U r).app (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom))
            (hT.tmul i j' (Opposite.op W.left) ((M.piece i).val.map W.hom.op x) y) := fun r =>
      hT.universal_app L n U (hG.sectionsEquiv n U r) i j' k (by omega)
        (Over.mk (W.hom ≫ V.hom)) ((M.piece i).val.map W.hom.op x) y
    rw [e, e, e]
    exact hG.sectionsEquiv_add n U p q (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom)) _
  sectionsEquiv_smul n U r p i j hij V x := by
    refine hH.symm_smul j V.left _ _ _ fun j' k hj'k W y => ?_
    have e : ∀ pp : (G n).val.obj (Opposite.op U),
        (balancedHom (hT.universal L n U (hG.sectionsEquiv n U pp)) hij V x).app j' k hj'k W y =
          (hG.sectionsEquiv n U pp).app (i + j') k (by omega) (Over.mk (W.hom ≫ V.hom))
            (hT.tmul i j' (Opposite.op W.left) ((M.piece i).val.map W.hom.op x) y) := fun pp =>
      hT.universal_app L n U (hG.sectionsEquiv n U pp) i j' k (by omega)
        (Over.mk (W.hom ≫ V.hom)) ((M.piece i).val.map W.hom.op x) y
    have hr : R.obj.map (Over.mk (W.hom ≫ V.hom)).hom.op r =
        R.obj.map W.hom.op (R.obj.map V.hom.op r) := ring_map_comp_op W.hom V.hom r
    rw [e, e, hG.sectionsEquiv_smul n U r p (i + j') k (by omega)
      (Over.mk (W.hom ≫ V.hom)), hr]
  sectionsEquiv_naturality n {U U'} q p i j hij V := by
    have hres : hG.sectionsEquiv n U' ((G n).val.map q.op p) =
        (hG.sectionsEquiv n U p).restrict q :=
      GradedLocalHom.ext fun i' j' hij' V' x =>
        DFunLike.congr_fun (hG.sectionsEquiv_naturality n q p i' j' hij' V') x
    have huniv : hT.universal L n U' (hG.sectionsEquiv n U' ((G n).val.map q.op p)) =
        (hT.universal L n U (hG.sectionsEquiv n U p)).restrict q := by
      rw [hres]
      refine GradedLocalBalanced.ext fun i' j' k hijk V' x y => ?_
      rw [GradedLocalBalanced.restrict_app,
        ← hT.universal_restrict L n q (hG.sectionsEquiv n U p) i' j' k hijk V' x y]
    have key : ofBalanced hH (hT.universal L n U'
          (hG.sectionsEquiv n U' ((G n).val.map q.op p))) =
        (ofBalanced hH (hT.universal L n U (hG.sectionsEquiv n U p))).restrict q := by
      rw [ofBalanced_restrict, huniv]
    exact congrArg (fun z : GradedLocalHom M H n U' => z.app i j hij V) key

end SheafOfModules

end
