module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentials.Basic

/-!
# Derivations along the comorphism are derivations along the structural map

Let `f : X ⟶ S` be a morphism of schemes and let `M` be a sheaf of `𝒪_X`-modules. A relative
derivation of `𝒪_X` in the sense of the sheaf of relative differentials is a derivation
relative to the structural map `f⁻¹ 𝒪_S ⟶ 𝒪_X`, so its vanishing condition is stated on
sections of an inverse image sheaf — a sheafified colimit, whose sections are not directly
computable. The usable condition is the one on the comorphism `f.c`, which only sees sections
coming from a single open of `S`. `Stacks.AlgebraicGeometry.AffineDifferentials` transports a
derivation in the first sense to one in the second; this file proves the converse, which is
the direction that a construction of relative derivations out of ring data needs.

## Main definitions

* `constantsSubring`, `constants`, `constantsι`: the sections annihilated by a derivation, as
  a subring, as a subpresheaf of rings and with its inclusion. Stated for a derivation along a
  morphism `O₁ ⟶ F.op ⋙ O₂` of presheaves of commutative rings over categories related by a
  functor `F`, which is the generality the comorphism of a morphism of schemes lives in.
* `constantsSheaf` and `constantsSheafι`: the same on a scheme, where the constants form a
  genuine subsheaf of rings of `𝒪_X`.
* `comorphismToConstants`: the factorization of `f.c` through the pushforward of that subsheaf.
* `toStructuralDerivation`: a derivation along `f.c` read as a derivation along
  `f⁻¹ 𝒪_S ⟶ 𝒪_X`.

## Main results

* `constants_isSheaf`: the constants of a derivation with values in a *sheaf* of modules form
  a sheaf of rings.
* `d_inverseImageStructureMap_eq_zero`: a derivation along the comorphism annihilates the whole
  image of the structural map.

## Implementation notes

No local-surjectivity analysis of the inverse image sheaf is needed, and that is the point.
The sections of `𝒪_X` annihilated by a derivation form a subring, because a derivation sends
`1` to `0` and satisfies the Leibniz rule, and they form a *subsheaf* because the target is a
sheaf of modules and so is separated: a section whose restrictions to a cover are annihilated
is annihilated. The vanishing condition on the comorphism says exactly that `f.c` factors
through the pushforward of that subsheaf, so by the adjunction `f⁻¹ ⊣ f_*` defining the
structural map, the structural map factors through the subsheaf as well, and every section in
its image is annihilated. This is the argument of
`Stacks.Sheaves.RingedSpaceDifferentials.derivation_d_inverseImageStructureMap_eq_zero`, which
is stated for ringed spaces and for a derivation along a morphism of presheaves of rings over
one index category; the comorphism of a morphism of schemes relates two different index
categories, so the constants construction is redone here at that generality, over an arbitrary
functor `F`, and the sheaf condition is taken from the scheme's own structure sheaf.

Mathlib records the comparison of the two vanishing conditions as the open problem left by
`Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf`, whose header says that the
general case of the module of differentials "shall be obtained by observing that derivations
for `S ⟶ F.op ⋙ R` identify to derivations for `S' ⟶ R` ... it suffices to show that the two
vanishing conditions `d_app` are equivalent". `toStructuralDerivation` together with
`AffineDifferentials.comorphismDerivation` is that equivalence for the structural map of a
morphism of schemes.

Everything is in a single universe: the schemes are in `Scheme.{u}` and `X.Modules` is
`SheafOfModules.{u} X.ringCatSheaf`, so no universe side condition arises. The generic
`constants` section is polymorphic in the two index categories and their hom universes, and
the sheaf section fixes the space and the rings to one universe because
`TopCat.Presheaf.IsSheaf` relates them.

Two transparency points. The constants construction is stated for a
general presheaf of modules over an abstract presheaf of rings rather than directly for
`M.val` with `M : X.Modules`: at the latter spelling the ring presheaf is reached through
`X.ringCatSheaf`, which is a definition, and the module and scalar instances on the sections
then come by a path that `rw` does not see, so even `smul_zero` fails to fire inside the
subring proof. Instantiating the generic version at the scheme later costs nothing.
Relatedly, the factorization of the structural map is obtained by producing the factoring
morphism with `Exists.elim` and then applying `congrArg` to it, rather than by rewriting
inside a goal that mentions the underlying presheaf of a sheaf of rings, since `TopCat.Sheaf`
is a definition and such a goal is not type-correct at implicit transparency.

## What is not done here

Nothing about affine opens, and nothing about the sheaf of relative differentials beyond the
two readings of a derivation: this file does not construct any derivation, it only transports
the vanishing condition.

## References

* [Stacks Project, Tag 01UO](https://stacks.math.columbia.edu/tag/01UO)
* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
* [Stacks Project, Tag 0H79](https://stacks.math.columbia.edu/tag/0H79)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v w w' u₁ u₂

namespace Stacks.AlgebraicGeometry.AffineDifferentialsIso

/-! ### The sheaf of constants of a derivation -/

section Constants

variable {C₁ : Type u₁} [Category.{w} C₁] {C₂ : Type u₂} [Category.{w'} C₂] {F : C₁ ⥤ C₂}
  {O₁ : C₁ᵒᵖ ⥤ CommRingCat.{v}} {O₂ : C₂ᵒᵖ ⥤ CommRingCat.{v}} {φ : O₁ ⟶ F.op ⋙ O₂}
  {M : PresheafOfModules.{v} (O₂ ⋙ forget₂ CommRingCat.{v} RingCat.{v})}
  (D : PresheafOfModulesOfCommRing.Derivation M φ)

/-- The subring of sections annihilated by a derivation. It is a subring because a derivation
sends `1` to `0` and satisfies the Leibniz rule. -/
def constantsSubring (U : C₂ᵒᵖ) : Subring (O₂.obj U) where
  carrier := {a | D.d a = 0}
  mul_mem' {a b} ha hb := by
    have h := D.d_mul a b
    rwa [show D.d a = 0 from ha, show D.d b = 0 from hb, smul_zero, smul_zero, add_zero] at h
  one_mem' := D.d_one U
  add_mem' {a b} ha hb := by
    have h := map_add D.d a b
    rwa [show D.d a = 0 from ha, show D.d b = 0 from hb, add_zero] at h
  zero_mem' := map_zero D.d
  neg_mem' {a} ha := by
    have h := map_neg D.d a
    rwa [show D.d a = 0 from ha, neg_zero] at h

/-- Membership in `constantsSubring` is being annihilated by the derivation. -/
theorem mem_constantsSubring {U : C₂ᵒᵖ} (a : O₂.obj U) :
    a ∈ constantsSubring D U ↔ D.d a = 0 := Iff.rfl

/-- The presheaf of commutative rings of sections annihilated by a derivation. It is a
subpresheaf of rings of the ambient presheaf because a derivation commutes with restriction. -/
@[simps obj]
def constants : C₂ᵒᵖ ⥤ CommRingCat.{v} where
  obj U := CommRingCat.of (constantsSubring D U)
  map {U V} i := CommRingCat.ofHom
    { toFun a := ⟨(O₂.map i) a.1, by
        have h := D.d_map i a.1
        rwa [show D.d a.1 = 0 from a.2, map_zero] at h⟩
      map_one' := Subtype.ext (by simp)
      map_mul' a b := Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' a b := Subtype.ext (by simp) }
  map_id U := by
    apply CommRingCat.hom_ext
    ext a
    exact congrArg (fun g => (ConcreteCategory.hom g) a.1) (O₂.map_id U)
  map_comp {U V W} i j := by
    apply CommRingCat.hom_ext
    ext a
    exact congrArg (fun g => (ConcreteCategory.hom g) a.1) (O₂.map_comp i j)

/-- The inclusion of the presheaf of sections annihilated by a derivation. -/
@[simps]
def constantsι : constants D ⟶ O₂ where
  app U := CommRingCat.ofHom (constantsSubring D U).subtype
  naturality _ _ _ := rfl

end Constants

/-! ### The constants form a sheaf -/

section Sheaf

variable {Z : TopCat.{u}} {C₁ : Type u₁} [Category.{w} C₁] {F : C₁ ⥤ Opens Z}
  {O₁ : C₁ᵒᵖ ⥤ CommRingCat.{u}} {O₂ : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u}}
  {φ : O₁ ⟶ F.op ⋙ O₂}
  {M : PresheafOfModules.{u} (O₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
  (hO : TopCat.Presheaf.IsSheaf O₂) (hM : TopCat.Presheaf.IsSheaf M.presheaf)
  (D : PresheafOfModulesOfCommRing.Derivation M φ)

include hO hM in
/-- The sections annihilated by a derivation with values in a *sheaf* of modules form a sheaf
of rings: a section is annihilated as soon as its restrictions to a cover are, because the
target is separated. -/
theorem constants_isSheaf : TopCat.Presheaf.IsSheaf (constants D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι W sf hsf
  have hsf' : TopCat.Presheaf.IsCompatible O₂ W (fun i => (sf i).1) := fun i j =>
    congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, huniq⟩ := hO.isSheafUniqueGluing W (fun i => (sf i).1) hsf'
  have hD : D.d s = 0 := by
    refine TopCat.Presheaf.IsSheaf.section_ext hM ?_
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨W i, le_iSup W i, hi, ?_⟩
    have h1 := D.d_map (homOfLE (le_iSup W i)).op s
    have h2 : (O₂.map (homOfLE (le_iSup W i)).op) s = (sf i).1 := hs i
    refine Eq.trans ?_ (map_zero _).symm
    exact h1.symm.trans ((congrArg D.d h2).trans (sf i).2)
  exact ⟨⟨s, hD⟩, fun i => Subtype.ext (hs i),
    fun t ht => Subtype.ext (huniq t.1 fun i => congrArg Subtype.val (ht i))⟩

end Sheaf

/-! ### The converse of `comorphismDerivation` -/

section Crux

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
  (D : PresheafOfModulesOfCommRing.Derivation M.val f.c)

/- A subsheaf of rings of `𝒪_X`, cut out inside the structure sheaf by `D`: the input is
exactly `f`, `M` and `D`.  The library's other sheaves of commutative rings of this form pair a
presheaf built from quite different data — the stalks at the generic points, a quasi-regular
presentation, an equalizer of two algebra morphisms, a square-zero extension by a module, a
concrete subalgebra, a sheafified topological pullback — with its own sheaf condition. -/

/-- The subsheaf of rings of `𝒪_X` of sections annihilated by a derivation of the structure
sheaf along the comorphism of `f`, with values in a sheaf of modules. -/
def constantsSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  ⟨constants D, constants_isSheaf X.sheaf.property M.isSheaf D⟩

/-- The inclusion of the subsheaf of constants into the structure sheaf. -/
def constantsSheafι : constantsSheaf f M D ⟶ X.sheaf := ObjectProperty.homMk (constantsι D)

/-- The comorphism of `f` factors through the sheaf of constants of a derivation along it. -/
def comorphismToConstants : S.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj (constantsSheaf f M D) :=
  ObjectProperty.homMk
    { app V := CommRingCat.ofHom
        { toFun b := ⟨(f.c.app V).hom b, D.d_app b⟩
          map_one' := Subtype.ext (map_one _)
          map_mul' a b := Subtype.ext (map_mul _ a b)
          map_zero' := Subtype.ext (map_zero _)
          map_add' a b := Subtype.ext (map_add _ a b) }
      naturality V W i := by
        apply CommRingCat.hom_ext
        ext b
        exact Subtype.ext
          (congrArg (fun g => (ConcreteCategory.hom g) b) (f.c.naturality i)) }

/-- `comorphismToConstants` is a factorization of the comorphism. -/
theorem comorphismToConstants_comp :
    comorphismToConstants f M D ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).map
      (constantsSheafι f M D) = (⟨f.c⟩ :
        S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf) :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun _ => rfl))

/-- A derivation of the structure sheaf of `X` along the comorphism of `f`, with values in a
sheaf of modules, annihilates the whole image of the structural map `f⁻¹ 𝒪_S ⟶ 𝒪_X`. -/
theorem d_inverseImageStructureMap_eq_zero (W : (Opens X)ᵒᵖ)
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf).presheaf.obj W) :
    D.d (((inverseImageStructureMap f).hom.app W).hom a) = 0 := by
  have key : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv
          S.sheaf (constantsSheaf f M D)).symm (comorphismToConstants f M D) ≫
        constantsSheafι f M D = inverseImageStructureMap f := by
    rw [inverseImageStructureMap, ← comorphismToConstants_comp f M D,
      Adjunction.homEquiv_naturality_right_symm]
  obtain ⟨σ, hσ⟩ : ∃ σ : (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶
      constantsSheaf f M D, σ ≫ constantsSheafι f M D = inverseImageStructureMap f := ⟨_, key⟩
  have h3 := congrArg
    (fun (g : (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶ X.sheaf) =>
      (g.hom.app W).hom a) hσ
  exact (congrArg D.d h3.symm).trans ((σ.hom.app W).hom a).2

/-- A derivation of the structure sheaf of `X` along the comorphism of `f`, with values in a
sheaf of modules, read as a derivation relative to the structural map `f⁻¹ 𝒪_S ⟶ 𝒪_X`. The
underlying additive maps and the Leibniz and restriction-compatibility data are unchanged;
only the vanishing condition is transported. This is the converse of
`Stacks.AlgebraicGeometry.AffineDifferentials.comorphismDerivation`. -/
def toStructuralDerivation : SheafOfModules.SheafDerivation (inverseImageStructureMap f) M where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {W} a := d_inverseImageStructureMap_eq_zero f M D W a

/-- Reading a derivation along the comorphism as a derivation along the structural map does
not change its underlying additive map on an open. -/
theorem toStructuralDerivation_d (W : X.Opens) :
    (toStructuralDerivation f M D).d (X := op W) = D.d := rfl

end Crux

end Stacks.AlgebraicGeometry.AffineDifferentialsIso

end
