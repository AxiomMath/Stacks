module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# The isomorphism locus of the second map of a right-exact sequence of quasi-coherent modules

Let `F ⟶ G ⟶ H ⟶ 0` be an exact sequence of quasi-coherent `𝒪_X`-modules on an algebraic
space `X` over an algebraic space `Y`, with maps `u : F ⟶ G` and `v : G ⟶ H`.  Each of the two
maps is the datum of a situation of Stacks 083F for the same morphism `X ⟶ Y`, so each has its
four base-change loci.  Pullback of modules is a left adjoint, hence right exact, so on every
test scheme `T` over `Y` the base-changed sequence `F_T ⟶ G_T ⟶ H_T ⟶ 0` is again exact; in
particular `v_T` is always an epimorphism, and it is an isomorphism exactly when its kernel —
the image of `u_T` — vanishes, that is exactly when `u_T = 0`.  Stacks 0CVM records this as the
equality of loci `F_{v,iso} = F_{u,zero}`.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackSystem` assembles the inverse image of `𝒪`-modules
  along a morphism of algebraic spaces into a
  `AlgebraicGeometry.Space.ModulePullbackSystem`, the data the base-change loci of Stacks 083F
  consume.
* `AlgebraicGeometry.Space.ModuleMapSituation.secondMap` reads the second map of a sequence of
  modules as a situation of Stacks 083F in its own right.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isIsoAt_secondMap_iff_isZeroAt`: at a test
  scheme, the base change of the second map of a right-exact sequence is an isomorphism exactly
  when the base change of the first map is zero.
* `AlgebraicGeometry.Space.ModuleMapSituation.isoFunctor_secondMap_eq_zeroFunctor` is
  Stacks 0CVM: the isomorphism locus of the second map and the vanishing locus of the first map
  are the same subterminal functor on the schemes over `Y`.

## Implementation notes

Both statements are at the module universe of the structure rings, because that is the universe
at which `AlgebraicGeometry.Space.modulePullback` and its adjunction are available, and hence
the universe at which `AlgebraicGeometry.Space.modulePullbackSystem` can be built; the loci
themselves stay universe-polymorphic in the module universe.

The engine of the proof is two facts of homological algebra that hold in any abelian category:
that an exact `A ⟶ B ⟶ C` with `B ⟶ C` an epimorphism has `B ⟶ C` an isomorphism exactly when
`A ⟶ B` is zero, and that a functor preserving zero morphisms and finite colimits carries such
a sequence to another one.  Both are kept private, as is the bookkeeping that recognises the
loci of the two situations as instances of
`AlgebraicGeometry.Space.ModuleMapSituation.subterminalFunctor` for a common test category —
all but `AlgebraicGeometry.Space.ModuleMapSituation.subterminalFunctor_congr`, that two such
instances attached to equal properties agree, which the other locus files share.

## References

* [Stacks Project, Tag 0CVM](https://stacks.math.columbia.edu/tag/0CVM)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The pullback of modules as a system -/

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces over `S`, packaged as
a `AlgebraicGeometry.Space.ModulePullbackSystem`: the functors are
`AlgebraicGeometry.Space.modulePullback`, the composition comparisons are
`AlgebraicGeometry.Space.modulePullbackCompIso`, and the two exactness properties hold because
each functor is a left adjoint. -/
def modulePullbackSystem : ModulePullbackSystem.{u, u} B S hS where
  functor f := modulePullback B S hS f
  compIso f g := modulePullbackCompIso B S hS f g
  preservesZeroMorphisms f :=
    have := (modulePullbackAdjunction B S hS f).isLeftAdjoint
    inferInstance
  preservesEpimorphisms f :=
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS f)

/-- The functors of `AlgebraicGeometry.Space.modulePullbackSystem` are the inverse images of
`𝒪`-modules. -/
@[simp]
theorem modulePullbackSystem_functor {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (modulePullbackSystem B S hS).functor f = modulePullback B S hS f :=
  rfl

/-! ### Right-exact sequences in an abelian category -/

section RightExact

universe v₁ u₁ v₂ u₂

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]

/-- In an abelian category, the second map of an exact sequence `A ⟶ B ⟶ C` whose second map is
an epimorphism is an isomorphism exactly when the first map is zero. -/
private lemma isIso_g_iff_f_eq_zero (T : ShortComplex C₁) (hT : T.Exact) (hepi : Epi T.g) :
    IsIso T.g ↔ T.f = 0 := by
  constructor
  · intro h
    rw [← cancel_mono T.g, T.zero, zero_comp]
  · intro h
    exact CokernelCofork.IsColimit.isIso_π _
      (T.exact_and_epi_g_iff_g_is_cokernel.1 ⟨hT, hepi⟩).some h

/-- A functor between abelian categories preserving zero morphisms and finite colimits carries
an exact sequence `A ⟶ B ⟶ C` whose second map is an epimorphism to another such sequence. -/
private lemma exact_map_and_epi_map (F : C₁ ⥤ C₂) [F.PreservesZeroMorphisms]
    [PreservesFiniteColimits F] (T : ShortComplex C₁) (hT : T.Exact) (hepi : Epi T.g) :
    (T.map F).Exact ∧ Epi (F.map T.g) :=
  (T.map F).exact_and_epi_g_iff_g_is_cokernel.2
    ⟨CokernelCofork.mapIsColimit _ (T.exact_and_epi_g_iff_g_is_cokernel.1 ⟨hT, hepi⟩).some F⟩

end RightExact

/-! ### The second map of a sequence as a situation -/

namespace ModuleMapSituation

variable {B S hS}

/-- The second map `v : G ⟶ H` of a sequence `F ⟶ G ⟶ H` of quasi-coherent `𝒪_X`-modules, read
as a situation of Stacks 083F for the same morphism `X ⟶ Y`: its source module is the target
module of the given situation. -/
def secondMap (D : ModuleMapSituation.{u, m} B S hS)
    (H : Modules.{u, m} B S hS D.X.1 D.X.2) (hH : H.IsQuasicoherentOnSite) (v : D.G ⟶ H) :
    ModuleMapSituation.{u, m} B S hS where
  X := D.X
  Y := D.Y
  f := D.f
  F := D.G
  G := H
  quasicoherent_F := D.quasicoherent_G
  quasicoherent_G := hH
  u := v

/-- Two subterminal functors on the same test category attached to equal properties agree. -/
theorem subterminalFunctor_congr (D : ModuleMapSituation.{u, m} B S hS)
    {Q Q' : D.SchemesOver → Prop}
    (stable : ∀ {T T' : D.SchemesOver}, (T' ⟶ T) → Q T → Q T')
    (stable' : ∀ {T T' : D.SchemesOver}, (T' ⟶ T) → Q' T → Q' T') (hQ : Q = Q') :
    D.subterminalFunctor Q stable = D.subterminalFunctor Q' stable' := by
  subst hQ
  rfl

/-- The base-change loci of the second map and of the first map are read off the same pullback
functor, so the pointwise comparison of the two conditions is literally a comparison of the
pulled-back maps. -/
private lemma isIsoAt_secondMap_iff_isZeroAt_of (D : ModuleMapSituation.{u, m} B S hS)
    (P : ModulePullbackSystem.{u, m} B S hS)
    (H : Modules.{u, m} B S hS D.X.1 D.X.2) (hH : H.IsQuasicoherentOnSite) (v : D.G ⟶ H)
    (T : D.SchemesOver)
    (h : IsIso ((P.functor (D.baseChangeProjection T)).map v) ↔
      (P.functor (D.baseChangeProjection T)).map D.u = 0) :
    (D.secondMap H hH v).IsIsoAt P T ↔ D.IsZeroAt P T :=
  h

/-- The pointwise comparison of the two conditions upgrades to an equality of the two
subterminal functors. -/
private lemma isoFunctor_secondMap_eq_zeroFunctor_of (D : ModuleMapSituation.{u, m} B S hS)
    (P : ModulePullbackSystem.{u, m} B S hS)
    (H : Modules.{u, m} B S hS D.X.1 D.X.2) (hH : H.IsQuasicoherentOnSite) (v : D.G ⟶ H)
    (h : ∀ T : D.SchemesOver, (D.secondMap H hH v).IsIsoAt P T ↔ D.IsZeroAt P T) :
    (D.secondMap H hH v).isoFunctor P = D.zeroFunctor P :=
  subterminalFunctor_congr D (fun g hT => (D.secondMap H hH v).isIsoAt_of_hom P g hT)
    (fun g hT => D.isZeroAt_of_hom P g hT) (funext fun T => propext (h T))

/-! ### Stacks 0CVM -/

/-- **Stacks 0CVM**, pointwise.  For an exact sequence `F ⟶ G ⟶ H ⟶ 0` of quasi-coherent
`𝒪_X`-modules and a scheme `T` over `Y`, the base change of `v : G ⟶ H` to `X ×_Y T` is an
isomorphism exactly when the base change of `u : F ⟶ G` is zero. -/
@[stacks 0CVM "pointwise"]
theorem isIsoAt_secondMap_iff_isZeroAt (D : ModuleMapSituation.{u, u} B S hS)
    (H : Modules.{u, u} B S hS D.X.1 D.X.2) (hH : H.IsQuasicoherentOnSite)
    (v : D.G ⟶ H) (hcomp : D.u ≫ v = 0)
    (hexact : (ShortComplex.mk D.u v hcomp).Exact) [Epi v] (T : D.SchemesOver) :
    (D.secondMap H hH v).IsIsoAt (modulePullbackSystem B S hS) T ↔
      D.IsZeroAt (modulePullbackSystem B S hS) T := by
  refine isIsoAt_secondMap_iff_isZeroAt_of D (modulePullbackSystem B S hS) H hH v T ?_
  rw [modulePullbackSystem_functor]
  have hadj := modulePullbackAdjunction B S hS (D.baseChangeProjection T)
  have := hadj.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS (D.baseChangeProjection T)) :=
    hadj.leftAdjoint_preservesColimits
  obtain ⟨hex, hep⟩ := exact_map_and_epi_map (modulePullback B S hS (D.baseChangeProjection T))
    (ShortComplex.mk D.u v hcomp) hexact ‹Epi v›
  exact isIso_g_iff_f_eq_zero _ hex hep

/-- **Stacks 0CVM.**  For an exact sequence `F ⟶ G ⟶ H ⟶ 0` of quasi-coherent `𝒪_X`-modules,
the locus of schemes over `Y` where the base change of `v : G ⟶ H` is an isomorphism coincides
with the locus where the base change of `u : F ⟶ G` vanishes. -/
@[stacks 0CVM]
theorem isoFunctor_secondMap_eq_zeroFunctor (D : ModuleMapSituation.{u, u} B S hS)
    (H : Modules.{u, u} B S hS D.X.1 D.X.2) (hH : H.IsQuasicoherentOnSite)
    (v : D.G ⟶ H) (hcomp : D.u ≫ v = 0)
    (hexact : (ShortComplex.mk D.u v hcomp).Exact) [Epi v] :
    (D.secondMap H hH v).isoFunctor (modulePullbackSystem B S hS) =
      D.zeroFunctor (modulePullbackSystem B S hS) :=
  isoFunctor_secondMap_eq_zeroFunctor_of D (modulePullbackSystem B S hS) H hH v
    fun T => D.isIsoAt_secondMap_iff_isZeroAt H hH v hcomp hexact T

end ModuleMapSituation

end AlgebraicGeometry.Space

end
