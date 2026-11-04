module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# The ambient factor of the canonical map of conormal algebras

Let
```
Z --i--→ X
         |
         g
         ↓
         X'
```
be a morphism `i : Z ⟶ X` of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, followed by a morphism `g : X ⟶ X'`.  Write `𝓘 = Ker(i^♯) ⊆ 𝒪_X` and
`𝓙 = Ker((i ≫ g)^♯) ⊆ 𝒪_{X'}` for the kernel ideal sheaves of
`AlgebraicGeometry.Space.kernelIdealSheaf`.  Pullback of regular functions along `g` carries
every power of `𝓙` into the corresponding power of `𝓘`.  This file constructs the resulting
degreewise map

`𝒞_{Z/X',n} = (i ≫ g)^*(𝓙ⁿ) ⟶ i^*(𝓘ⁿ) = 𝒞_{Z/X,n}`,

the factor replacing the ambient space `X'` by `X` of the canonical map of conormal algebras of
[Stacks Project, Tag 09RS].

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap`: the chartwise linear map of sections along
  `g` from the `n`-th power of `𝓙` to the `n`-th power of `𝓘`, given by pullback of regular
  functions along the vertical morphism of a chart diagram.
* `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap`: the morphism `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` of
  `𝒪_X`-modules obtained from it by transposing twice.
* `AlgebraicGeometry.Space.conormalAlgebraAmbientPieceMap`: the degree-`n` component
  `𝒞_{Z/X',n} ⟶ 𝒞_{Z/X,n}` of the ambient factor.

## Main results

* `AlgebraicGeometry.Space.mem_kernelIdealSheaf_chartDiagramPullback`: pullback of regular
  functions along the vertical morphism of a chart diagram over `g` carries the kernel ideal of
  `i ≫ g` into the kernel ideal of `i`.
* `AlgebraicGeometry.Space.mem_kernelIdealSheaf_pow_chartDiagramPullback`: the same for the
  powers of the ideals of sections.
* `AlgebraicGeometry.Space.mem_idealSheafPow_kernelIdealSheaf_chartDiagramPullback` and
  `AlgebraicGeometry.Space.mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback`: the same
  for the powers of the sheaves of ideals, for natural and for integer exponents.
* `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap_app_coe` and
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_transpose`: the chartwise formula for
  the linear map of sections, and the characterising property of the morphism of modules built
  from it.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X X' : AlgebraicSpaces B S hS} (i : Z ⟶ X) (g : X ⟶ X')

/-- A homomorphism of rings carrying an ideal into an ideal carries the powers into the powers:
a sum of `n`-fold products of elements of the first ideal goes to a sum of `n`-fold products of
elements of the second. -/
private theorem mem_pow_of_ringHom {A C : Type*} [Ring A] [Ring C] (φ : A →+* C)
    {I : Ideal A} {K : Ideal C} (h : ∀ a ∈ I, φ a ∈ K) (n : ℕ) {x : A} (hx : x ∈ I ^ n) :
    φ x ∈ K ^ n := by
  induction n generalizing x with
  | zero =>
    rw [Submodule.pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    rw [Submodule.pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun y z hy hz ↦ ?_)
    · rw [map_mul, Submodule.pow_succ]
      exact Submodule.mul_mem_mul (ih ha) (h b hb)
    · rw [map_add]
      exact add_mem hy hz

/-! ### The kernel ideal sheaf along a chart diagram -/

/-- Let `d` be a commutative diagram of étale scheme charts over `g`, with chart `U` of `X` and
chart `V` of `X'`.  Then pullback of regular functions along the vertical morphism of `d` carries a
function on `V` killed by `(i ≫ g)^♯` to a function on `U` killed by `i^♯`. -/
theorem mem_kernelIdealSheaf_chartDiagramPullback
    (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    {s : ToType ((structureRingSheaf B S hS X').obj.obj (op d.V))}
    (hs : s ∈ SheafOfModules.idealAt (kernelIdealSheaf B S hS (i ≫ g)) (op d.V)) :
    (chartDiagramPullback B S hS g d).hom s ∈
      SheafOfModules.idealAt (kernelIdealSheaf B S hS i) (op d.U) := by
  have hig : (i ≫ g).hom = i.hom ≫ g.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
  refine (mem_ker_structureSharp_iff B S hS i d.U _).2 fun j => ?_
  have hc : (unop j.right).1.hom ≫ i.hom =
      yoneda.map (chartBaseChangeMap B S hS i d.U j) ≫ d.U.1.hom :=
    (chartDiagramOfIndex B S hS i d.U j).comm
  have hcomm : (unop j.right).1.hom ≫ (i ≫ g).hom =
      yoneda.map (chartBaseChangeMap B S hS i d.U j ≫ d.g) ≫ d.V.1.hom := by
    rw [Functor.map_comp, Category.assoc, ← d.comm, ← reassoc_of% hc, hig]
  have hz : s ∈ RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (chartBaseChangeMap B S hS i d.U j ≫ d.g)).op).hom :=
    kernelIdealSheaf_le_ker_of_chart B S hS (i ≫ g) d.V (unop j.right)
      (chartBaseChangeMap B S hS i d.U j ≫ d.g) hcomm hs
  have hsplit : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (chartBaseChangeMap B S hS i d.U j ≫ d.g)).op =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (chartBaseChangeMap B S hS i d.U j)).op := by
    rw [Functor.map_comp, op_comp, Functor.map_comp]
  rwa [hsplit] at hz

/-- For a commutative diagram `d` of étale scheme charts over `g`, pullback of regular functions
along the vertical morphism of `d` carries the `n`-th power of the kernel ideal of `(i ≫ g)^♯` over
the chart of `X'` into the `n`-th power of the kernel ideal of `i^♯` over the chart of `X`. -/
theorem mem_kernelIdealSheaf_pow_chartDiagramPullback
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (n : ℕ)
    {s : ToType ((structureRingSheaf B S hS X').obj.obj (op d.V))}
    (hs : s ∈ (SheafOfModules.idealAt (kernelIdealSheaf B S hS (i ≫ g)) (op d.V) :
      Ideal (ToType ((structureRingSheaf B S hS X').obj.obj (op d.V)))) ^ n) :
    (chartDiagramPullback B S hS g d).hom s ∈
      (SheafOfModules.idealAt (kernelIdealSheaf B S hS i) (op d.U) :
        Ideal (ToType ((structureRingSheaf B S hS X).obj.obj (op d.U)))) ^ n :=
  mem_pow_of_ringHom (chartDiagramPullback B S hS g d).hom
    (fun _ ha => mem_kernelIdealSheaf_chartDiagramPullback B S hS i g d ha) n hs

/-! ### The powers of the kernel ideal sheaf along a chart diagram -/

/-- For a commutative diagram `d` of étale scheme charts over `g`, pullback of regular functions
along the vertical morphism of `d` carries a section of the `n`-th power `𝓙ⁿ` of the kernel ideal
sheaf over the chart of `X'` to a section of `𝓘ⁿ` over the chart of `X`. -/
theorem mem_idealSheafPow_kernelIdealSheaf_chartDiagramPullback
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (n : ℕ)
    {s : ToType ((structureRingSheaf B S hS X').obj.obj (op d.V))}
    (hs : s ∈ SheafOfModules.idealAt
      (SheafOfModules.idealSheafPow (kernelIdealSheaf B S hS (i ≫ g)) n) (op d.V)) :
    (chartDiagramPullback B S hS g d).hom s ∈ SheafOfModules.idealAt
      (SheafOfModules.idealSheafPow (kernelIdealSheaf B S hS i) n) (op d.U) := by
  refine (SheafOfModules.mem_idealSheafPow_iff (kernelIdealSheaf B S hS i) n
    ((chartDiagramPullback B S hS g d).hom s)).2 ?_
  refine (SmallEtale.mem_topology_iff_exists_mem_range B S hS X.1
    (SheafOfModules.powSieve (kernelIdealSheaf B S hS i) n
      ((chartDiagramPullback B S hS g d).hom s))).2 fun z => ?_
  obtain ⟨V₀, m, hm, y, hy⟩ :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS X'.1
        (SheafOfModules.powSieve (kernelIdealSheaf B S hS (i ≫ g)) n s)).1
      ((SheafOfModules.mem_idealSheafPow_iff (kernelIdealSheaf B S hS (i ≫ g)) n s).1 hs)
      ((BigFppfOver.toScheme B S hS).map d.g z)
  obtain ⟨T, π, p, hp, hpm, w, hw, -⟩ :=
    exists_chart_pullback B S hS g d.U d.g d.comm.symm m z y hy.symm
  refine ⟨T, π, ?_, w, hw⟩
  let d' : ChartDiagram B S hS X.1 X'.1 g.hom := ⟨T, V₀, p, hp.symm⟩
  have hnat : (chartDiagramPullback B S hS g d').hom
        (((structureRingSheaf B S hS X').obj.map m.op).hom s) =
      ((structureRingSheaf B S hS X).obj.map π.op).hom
        ((chartDiagramPullback B S hS g d).hom s) := by
    have hcc : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X'.1).map m)).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map p).op =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X.1).map π)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← Functor.map_comp,
        ← Functor.map_comp, hpm]
    exact ConcreteCategory.congr_hom hcc s
  have key := mem_kernelIdealSheaf_pow_chartDiagramPullback B S hS i g d' n
    ((SheafOfModules.mem_powSieve_iff (kernelIdealSheaf B S hS (i ≫ g)) n s m).1 hm)
  rw [hnat] at key
  exact (SheafOfModules.mem_powSieve_iff (kernelIdealSheaf B S hS i) n
    ((chartDiagramPullback B S hS g d).hom s) π).2 key

/-- For a commutative diagram `d` of étale scheme charts over `g`, pullback of regular functions
along the vertical morphism of `d` carries a section of the integer-indexed power `𝓙ⁿ` over the
chart of `X'` to a section of `𝓘ⁿ` over the chart of `X`. -/
theorem mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback
    (d : ChartDiagram B S hS X.1 X'.1 g.hom) (n : ℤ)
    {s : ToType ((structureRingSheaf B S hS X').obj.obj (op d.V))}
    (hs : s ∈ SheafOfModules.idealAt
      (SheafOfModules.idealSheafZPow (kernelIdealSheaf B S hS (i ≫ g)) n) (op d.V)) :
    (chartDiagramPullback B S hS g d).hom s ∈ SheafOfModules.idealAt
      (SheafOfModules.idealSheafZPow (kernelIdealSheaf B S hS i) n) (op d.U) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [SheafOfModules.idealSheafZPow_of_neg _ hn,
      SheafOfModules.idealAt_zeroIdealSheaf] at hs
    have hz : (chartDiagramPullback B S hS g d).hom s = 0 := by
      rw [SheafOfModules.eq_zero_of_mem_bot hs]
      exact map_zero (chartDiagramPullback B S hS g d).hom
    rw [hz]
    exact zero_mem _
  · rw [SheafOfModules.idealSheafZPow_of_nonneg _ hn] at hs ⊢
    exact mem_idealSheafPow_kernelIdealSheaf_chartDiagramPullback B S hS i g d n.toNat hs

/-! ### The map of the powers of the kernel ideal sheaves -/

/-- The chartwise linear map of sections `𝓙ⁿ ⟶ 𝓘ⁿ` along `g`: on a commutative diagram of étale
scheme charts over `g` it is pullback of regular functions along the vertical morphism,
corestricted to the `n`-th powers of the two kernel ideal sheaves. -/
noncomputable def kernelIdealSheafZPowFMap (n : ℤ) :
    ModuleFMap B S hS g (kernelIdealSheafZPow B S hS i n).toSheafOfModules
      (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules where
  app d s := ⟨(chartDiagramPullback B S hS g d).hom s.1,
    mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback B S hS i g d n s.2⟩
  naturality d d' k j hkj s := by
    have hcc : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS X'.1).map j)).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d'.g).op =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            ((SmallEtale.toOver B S hS X.1).map k)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, ← Functor.map_comp,
        ← Functor.map_comp, hkj]
    exact Subtype.ext (ConcreteCategory.congr_hom hcc s.1)
  map_add d s t := Subtype.ext (map_add (chartDiagramPullback B S hS g d).hom s.1 t.1)
  map_smul d r s := Subtype.ext (map_mul (chartDiagramPullback B S hS g d).hom r s.1)

/-- The chartwise formula for `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap`: on a
commutative diagram of étale scheme charts over `g` it is pullback of regular functions along the
vertical morphism of the diagram. -/
theorem kernelIdealSheafZPowFMap_app_coe (n : ℤ) (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules.val.obj (op d.V)) :
    ((kernelIdealSheafZPowFMap B S hS i g n).app d s).1 =
      (chartDiagramPullback B S hS g d).hom s.1 :=
  rfl

/-- The map `g^*(𝓙ⁿ) ⟶ 𝓘ⁿ` of `𝒪_X`-modules: the transpose along the adjunction of
[Stacks Project, Tag 03D7] of the transpose along the chartwise universal property of the direct
image of `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap`. -/
noncomputable def kernelIdealSheafZPowPullbackMap (n : ℤ) :
    (modulePullback B S hS g).obj
        (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules ⟶
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules :=
  ((modulePullbackAdjunction B S hS g).homEquiv _ _).symm
    ((modulePushforwardHomEquiv B S hS g (kernelIdealSheafZPow B S hS i n).toSheafOfModules
      (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules).symm
        (kernelIdealSheafZPowFMap B S hS i g n))

/-- Transposing `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` back along the
Stacks 03D7 adjunction and then along the chartwise universal property of the direct image returns
the chartwise map `AlgebraicGeometry.Space.kernelIdealSheafZPowFMap`. -/
theorem kernelIdealSheafZPowPullbackMap_transpose (n : ℤ) :
    modulePushforwardHomEquiv B S hS g (kernelIdealSheafZPow B S hS i n).toSheafOfModules
        (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules
        ((modulePullbackAdjunction B S hS g).homEquiv _ _
          (kernelIdealSheafZPowPullbackMap B S hS i g n)) =
      kernelIdealSheafZPowFMap B S hS i g n := by
  rw [kernelIdealSheafZPowPullbackMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-! ### The ambient factor of the canonical map, degreewise -/

/-- The degree-`n` component of the ambient factor of the canonical map of
[Stacks Project, Tag 09RS], the map of `𝒪_Z`-modules

`𝒞_{Z/X',n} = (i ≫ g)^*(𝓙ⁿ) ⟶ i^*(𝓘ⁿ) = 𝒞_{Z/X,n}`.

It is the inverse image along `i` of `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap`,
read through the Stacks 03LU composition comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` which identifies `(i ≫ g)^*` with `i^*g^*`. -/
noncomputable def conormalAlgebraAmbientPieceMap (n : ℤ) :
    (conormalAlgebra B S hS (i ≫ g)).piece n ⟶ (conormalAlgebra B S hS i).piece n :=
  (modulePullbackCompIso B S hS i g).inv.app
      (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules ≫
    (modulePullback B S hS i).map (kernelIdealSheafZPowPullbackMap B S hS i g n)

/-- The degree-`n` component of the ambient factor, read on the inverse images of the powers of
the kernel ideal sheaves that the two conormal algebras are built from. -/
theorem conormalAlgebraAmbientPieceMap_eq (n : ℤ) :
    conormalAlgebraAmbientPieceMap B S hS i g n =
      (modulePullbackCompIso B S hS i g).inv.app
          (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules ≫
        (modulePullback B S hS i).map (kernelIdealSheafZPowPullbackMap B S hS i g n) :=
  rfl

end AlgebraicGeometry.Space

end
