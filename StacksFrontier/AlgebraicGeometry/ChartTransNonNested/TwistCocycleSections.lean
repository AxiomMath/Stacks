module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.RelativeProj
public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistSectionOn

/-!
# The nested twist cocycle on homogeneous sections

For a sheaf of graded algebras `A` on a scheme `S` and affine opens `W ≤ U`, the comparison
morphism `cmpNested` between the direct images of the twisting sheaves along the relative-Proj
charts of `W` and of `U` is computed on the homogeneous sections: it carries the restriction of
`degreeSection (A.grading U) k c` to the restriction of
`degreeSection (A.grading W) k (A.res h c)`. The comparison morphisms for a nested triple then
compose on those sections.

## Main results

* `cmpNested_degreeSection`: the computation, for every open of the relative Proj below the
  preimage of `W` and in every degree.
* `cmpNested_degreeSection_comp`: the cocycle identity on the homogeneous global sections of the
  chart of `U`, in every degree. This is the mathematical content of the nested-cocycle condition
  `IsNestedCocycle` for a sheaf of graded algebras.

## Implementation notes

Every junction here is stated at the level of variables and applied afterwards. That is not a
stylistic choice: each of `push_app_apply`, `push_app_apply_of`, `push_app_apply_top` and
`push_app_apply_cmp` exhausts the elaborator's recursion limit when stated at the
concrete instance, even as an unascribed `have`, and costs nothing at variables. There is
exactly one match against a written type in the file.

Two further measurements are recorded because they cost real time. The unit factor of
`pushNested` must be identified with the plain restriction map it is
(`pushNestedUnit_app_apply`) rather than with the unit of `restrictAdjunction`: the latter is
built by a tactic block, so a single delta of the definition exceeds the kernel's deterministic
timeout. And statements must write `((Scheme.Modules.pushforward f).obj M).val.map` rather than
the reducibly equal abbreviation `(pushforwardVal f M).map`, which sends the final match past
`maxRecDepth`.

## References

* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ChartTransNonNested
open Stacks.AlgebraicGeometry.ChartTransRelativeProj

namespace Stacks.AlgebraicGeometry.ChartTransRelativeProj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### Generic facts, at the level of variables -/

section Generic

variable {X : Scheme.{u}}

/-- A morphism whose component on the sections over an open is known to factor, read on a
section. The hypothesis has the shape of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested_app`. -/
public theorem app_apply_of_app_eq {M₀ M₁ M₂ : X.Modules} (ρ : M₀ ⟶ M₂) (a : M₀ ⟶ M₁) (b : M₁ ⟶ M₂)
    (V : X.Opens) (hρ : ρ.app V = a.app V ≫ b.app V) (s : M₀.val.obj (op V)) :
    ρ.val.app (op V) s = b.val.app (op V) (a.val.app (op V) s) :=
  congrArg (fun m : Γ(M₀, V) ⟶ Γ(M₂, V) => m s) hρ

/-- Naturality of a morphism of sheaves of modules, read on a section. -/
public theorem app_naturality {M N : X.Modules} (ψ : M ⟶ N) {T T' : X.Opens} (i : T' ⟶ T)
    (s : M.val.obj (op T)) :
    ψ.val.app (op T') (M.val.map i.op s) = N.val.map i.op (ψ.val.app (op T) s) :=
  PresheafOfModules.naturality_apply ψ.val i.op s

/-- Two restriction maps in a row are one: morphisms between opens are unique, so the composite
is a free argument. -/
public theorem map_map {M : X.Modules} {T₁ T₂ T₃ : X.Opens}
    (i : T₂ ⟶ T₁) (j : T₃ ⟶ T₂) (k : T₃ ⟶ T₁) (x : M.val.obj (op T₁)) :
    M.val.map j.op (M.val.map i.op x) = M.val.map k.op x := by
  obtain rfl : k = j ≫ i := Subsingleton.elim _ _
  exact (PresheafOfModules.map_comp_apply M.val i.op j.op x).symm

/-- Naturality against two restriction maps in a row. -/
public theorem app_map_map {M N : X.Modules} (ψ : M ⟶ N) {T₁ T₂ T₃ : X.Opens}
    (i : T₂ ⟶ T₁) (j : T₃ ⟶ T₂) (k : T₃ ⟶ T₁) (x : M.val.obj (op T₁)) :
    ψ.val.app (op T₃) (M.val.map j.op (M.val.map i.op x)) =
      N.val.map k.op (ψ.val.app (op T₁) x) :=
  (congrArg (ψ.val.app (op T₃)) (map_map i j k x)).trans (app_naturality ψ k x)

/-- Congruence in the section, under a restriction map followed by a morphism. -/
public theorem app_map_congr {M N : X.Modules} (ψ : M ⟶ N) {T T' : X.Opens}
    (i : T' ⟶ T) {x y : M.val.obj (op T)} (hxy : x = y) :
    ψ.val.app (op T') (M.val.map i.op x) = ψ.val.app (op T') (M.val.map i.op y) :=
  congrArg (fun z => ψ.val.app (op T') (M.val.map i.op z)) hxy

/-- Naturality against two restriction maps in a row, with the value of the morphism on the
section supplied. Every `congrArg` of a bundled morphism is performed here, at the level of
variables: at the concrete instance the same `congrArg` sends the elaborator past its heartbeat
budget at `isDefEq`. -/
public theorem app_map_map_of {M N : X.Modules} (ψ : M ⟶ N) {T₁ T₂ T₃ : X.Opens}
    (i : T₂ ⟶ T₁) (j : T₃ ⟶ T₂) (k : T₃ ⟶ T₁) (x : M.val.obj (op T₁))
    {y : N.val.obj (op T₁)} (hy : ψ.val.app (op T₁) x = y) :
    ψ.val.app (op T₃) (M.val.map j.op (M.val.map i.op x)) = N.val.map k.op y :=
  (app_map_map ψ i j k x).trans (congrArg (N.val.map k.op) hy)

/-- **A restriction map of a direct image is a restriction map of the module.** The containment
of the two preimages is a free argument. -/
public theorem pushforward_map_eq {X Y : Scheme.{u}} (f : Y ⟶ X) (M : Y.Modules) {V V₁ : X.Opens}
    (j : V ⟶ V₁) (j' : (f ⁻¹ᵁ V : Y.Opens) ⟶ f ⁻¹ᵁ V₁)
    (x : ((Scheme.Modules.pushforward f).obj M).val.obj (op V₁)) :
    ((Scheme.Modules.pushforward f).obj M).val.map j.op x = M.val.map j'.op x := by
  obtain rfl : j' = (Opens.map f.base).map j := Subsingleton.elim _ _
  rfl

/-- Congruence in the section, under a restriction map. -/
public theorem map_congr {M : X.Modules} {T T' : X.Opens} (i : T' ⟶ T)
    {x y : M.val.obj (op T)} (hxy : x = y) :
    M.val.map i.op x = M.val.map i.op y :=
  congrArg (M.val.map i.op) hxy

end Generic

/-! ### The bridge from the restriction unit to the pullback unit -/

section Bridge

variable {X Y : Scheme.{u}}

/-- **The bridge, read on a section over an arbitrary open.** The unit of the restriction
adjunction followed by the identification of restriction with pullback is the unit of the
pullback--pushforward adjunction, so it carries a section to the pulled-back section.

This is `Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback`
transported onto a section by `congrArg` of a function that evaluates a morphism. -/
public theorem restrictUnit_app (φ : X ⟶ Y) [IsOpenImmersion φ] (M : Y.Modules) (T : Y.Opens)
    (s : M.val.obj (op T)) :
    ((Scheme.Modules.restrictFunctorIsoPullback φ).hom.app M).val.app (op (φ ⁻¹ᵁ T))
        (((Scheme.Modules.restrictAdjunction φ).unit.app M).val.app (op T) s) =
      Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn φ M T s :=
  congrArg
    (fun ρ : M ⟶ (Scheme.Modules.pushforward φ).obj ((Scheme.Modules.pullback φ).obj M) =>
      ρ.val.app (op T) s)
    (Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback
      φ M)

/-- **The bridge with the unit written out as the restriction map it is.** The component of the
unit of the restriction adjunction over `T` is the restriction map from `T` to the image of its
preimage (`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`); this is that
substitution made once, at the level of variables.

It exists because the other spelling cannot be used at the concrete instance: identifying
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedUnit` with the pushforward of
`(restrictAdjunction _).unit.app _` exceeds the **kernel's** deterministic timeout,
while identifying it with a plain restriction map costs three seconds. -/
public theorem restrictUnit_app' (φ : X ⟶ Y) [IsOpenImmersion φ] (M : Y.Modules) (T : Y.Opens)
    (i₀ : (φ ''ᵁ (φ ⁻¹ᵁ T) : Y.Opens) ⟶ T) (s : M.val.obj (op T)) :
    ((Scheme.Modules.restrictFunctorIsoPullback φ).hom.app M).val.app (op (φ ⁻¹ᵁ T))
        (M.val.map i₀.op s) =
      Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn φ M T s := by
  obtain rfl : i₀ = homOfLE (φ.image_preimage_le T) := Subsingleton.elim _ _
  exact restrictUnit_app φ M T s

/-- Pulling a section back commutes with restriction. The containment of the two preimages is a
free argument. -/
public theorem pullbackSectionOn_map (φ : X ⟶ Y) (M : Y.Modules) {T T' : Y.Opens} (i : T' ⟶ T)
    (i' : (φ ⁻¹ᵁ T' : X.Opens) ⟶ φ ⁻¹ᵁ T) (s : M.val.obj (op T)) :
    Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn φ M T' (M.val.map i.op s) =
      ((Scheme.Modules.pullback φ).obj M).val.map i'.op
        (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn φ M T s) := by
  obtain rfl : i' = (Opens.map φ.base).map i := Subsingleton.elim _ _
  exact app_naturality ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M) i s

/-- **Pulling a global section back and restricting is restricting and then pulling back.** The
same statement as `pullbackSectionOn_map` with the source open taken to be `⊤` and
spelled `⊤` on both sides rather than as `φ ⁻¹ᵁ ⊤`.

The two are definitionally equal, and at the level of variables the identification is free — but
at the concrete instance below it is not: `φ ⁻¹ᵁ ⊤` for `φ` a `projInclusionMap` sends the
elaborator past its heartbeat budget at `whnf`. So the `⊤` spelling is fixed here, once, where
`φ` is a variable. -/
public theorem pullbackSection_map (φ : X ⟶ Y) (M : Y.Modules) (T' : Y.Opens) (i : T' ⟶ ⊤)
    (i' : (φ ⁻¹ᵁ T' : X.Opens) ⟶ ⊤) (s : M.val.obj (op ⊤)) :
    Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn φ M T' (M.val.map i.op s) =
      ((Scheme.Modules.pullback φ).obj M).val.map i'.op
        (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection φ M s) :=
  pullbackSectionOn_map φ M i i' s

end Bridge

/-! ### The nested comparison on a section, at the level of variables -/

section Push

variable {X Y Z : Scheme.{u}}

/-- **The three tail factors of the nested comparison on a section, at the level of variables.**
Pseudofunctoriality of the pushforward is the identity on sections, the chart congruence is a
restriction map along an equality of opens, and the last factor is the comparison of the two
charts. -/
public theorem tail_app_apply (φ : Z ⟶ Y) [IsOpenImmersion φ] (cU : Y ⟶ X) (cW : Z ⟶ X)
    (ht : φ ≫ cU = cW) (M : Y.Modules) (N : Z.Modules)
    (ι₂ : (Scheme.Modules.pullback φ).obj M ≅ N) (V : X.Opens)
    (i : (cW ⁻¹ᵁ V : Z.Opens) ⟶ φ ⁻¹ᵁ (cU ⁻¹ᵁ V))
    (w : ((Scheme.Modules.restrictFunctor φ).obj M).val.obj (op (φ ⁻¹ᵁ (cU ⁻¹ᵁ V)))) :
    ((Scheme.Modules.pushforwardComp φ cU).app ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
        (Scheme.Modules.pushforwardCongr ht).app ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
        (Scheme.Modules.pushforward cW).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback φ).app M ≪≫ ι₂)).hom.val.app (op V) w =
      ι₂.hom.val.app (op (cW ⁻¹ᵁ V))
        (((Scheme.Modules.restrictFunctorIsoPullback φ).hom.app M).val.app (op (cW ⁻¹ᵁ V))
          (((Scheme.Modules.restrictFunctor φ).obj M).val.map i.op w)) :=
  rfl

/-- **The nested comparison on a section, at the level of variables.** The four factors — the
unit of the restriction adjunction pushed forward, pseudofunctoriality of the pushforward, the
chart congruence, and the comparison of the two charts — carry a section over the preimage of `V`
in the larger chart to the comparison applied to the pulled-back section, restricted to the
preimage of `V` in the smaller chart.

Every ingredient is a variable: no scheme is a `Proj` and no module is a twist. The comparison
`ρ` and its two halves `a` and `b` are themselves variables, identified by `hρ`, `ha` and `hb`.
That is not economy. At the concrete instance, identifying `ρ` with the whole four-factor
composite underneath a `val.app` exceeds the **kernel's** deterministic timeout, and so does
identifying the first half `a` with the pushforward of the restriction adjunction's unit; what
does fit is `hρ` (which is proved, as `pushNested_app`), `hb`, and `ha` in the form below, where
the unit has already been replaced by the restriction map it is. -/
public theorem push_app_apply (φ : Z ⟶ Y) [IsOpenImmersion φ] (cU : Y ⟶ X) (cW : Z ⟶ X)
    (ht : φ ≫ cU = cW) (M : Y.Modules) (N : Z.Modules)
    (ι₂ : (Scheme.Modules.pullback φ).obj M ≅ N)
    (a : (Scheme.Modules.pushforward cU).obj M ⟶
      (Scheme.Modules.pushforward cU).obj
        ((Scheme.Modules.pushforward φ).obj ((Scheme.Modules.restrictFunctor φ).obj M)))
    (b : (Scheme.Modules.pushforward cU).obj
          ((Scheme.Modules.pushforward φ).obj ((Scheme.Modules.restrictFunctor φ).obj M)) ≅
      (Scheme.Modules.pushforward cW).obj N)
    (ρ : (Scheme.Modules.pushforward cU).obj M ⟶ (Scheme.Modules.pushforward cW).obj N)
    (V : X.Opens)
    (i₀ : (φ ''ᵁ (φ ⁻¹ᵁ (cU ⁻¹ᵁ V)) : Y.Opens) ⟶ cU ⁻¹ᵁ V)
    (i : (cW ⁻¹ᵁ V : Z.Opens) ⟶ φ ⁻¹ᵁ (cU ⁻¹ᵁ V))
    (hρ : ρ.app V = a.app V ≫ b.hom.app V)
    (ha : ∀ s : M.val.obj (op (cU ⁻¹ᵁ V)), a.val.app (op V) s = M.val.map i₀.op s)
    (hb : b = (Scheme.Modules.pushforwardComp φ cU).app
            ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
          (Scheme.Modules.pushforwardCongr ht).app
              ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
          (Scheme.Modules.pushforward cW).mapIso
            ((Scheme.Modules.restrictFunctorIsoPullback φ).app M ≪≫ ι₂))
    (s : M.val.obj (op (cU ⁻¹ᵁ V))) :
    ρ.val.app (op V) s =
      ι₂.hom.val.app (op (cW ⁻¹ᵁ V))
        (((Scheme.Modules.pullback φ).obj M).val.map i.op
          (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn φ M (cU ⁻¹ᵁ V) s)) := by
  refine Eq.trans (app_apply_of_app_eq ρ a b.hom V hρ s) ?_
  subst hb
  refine Eq.trans (tail_app_apply φ cU cW ht M N ι₂ V i _) ?_
  refine congrArg (ι₂.hom.val.app (op (cW ⁻¹ᵁ V))) ?_
  refine Eq.trans
    (app_naturality ((Scheme.Modules.restrictFunctorIsoPullback φ).hom.app M) i _) ?_
  refine congrArg (((Scheme.Modules.pullback φ).obj M).val.map i.op) ?_
  refine Eq.trans (congrArg
    (((Scheme.Modules.restrictFunctorIsoPullback φ).hom.app M).val.app
      (op (φ ⁻¹ᵁ (cU ⁻¹ᵁ V)))) (ha s)) ?_
  exact restrictUnit_app' φ M (cU ⁻¹ᵁ V) i₀ s

/-- **The nested comparison on the restriction of a global section, at the level of variables.**
The same as `push_app_apply` with the section taken to be the restriction of a global
section, and with the value of the comparison on the pulled-back global section supplied as the
hypothesis `hg`. The conclusion is then a restriction map applied to that value.

This is the form in which the concrete instance is used, and the reason it exists is the
measurement recorded on `push_app_apply`: every match of an inferred type against a
written one costs the kernel's whole budget at this instance, so the chain is assembled here,
where every ingredient is a variable, and instantiated exactly once. -/
public theorem push_app_apply_of (φ : Z ⟶ Y) [IsOpenImmersion φ] (cU : Y ⟶ X) (cW : Z ⟶ X)
    (ht : φ ≫ cU = cW) (M : Y.Modules) (N : Z.Modules)
    (ι₂ : (Scheme.Modules.pullback φ).obj M ≅ N)
    (a : (Scheme.Modules.pushforward cU).obj M ⟶
      (Scheme.Modules.pushforward cU).obj
        ((Scheme.Modules.pushforward φ).obj ((Scheme.Modules.restrictFunctor φ).obj M)))
    (b : (Scheme.Modules.pushforward cU).obj
          ((Scheme.Modules.pushforward φ).obj ((Scheme.Modules.restrictFunctor φ).obj M)) ≅
      (Scheme.Modules.pushforward cW).obj N)
    (ρ : (Scheme.Modules.pushforward cU).obj M ⟶ (Scheme.Modules.pushforward cW).obj N)
    (V : X.Opens)
    (i₀ : (φ ''ᵁ (φ ⁻¹ᵁ (cU ⁻¹ᵁ V)) : Y.Opens) ⟶ cU ⁻¹ᵁ V)
    (i : (cW ⁻¹ᵁ V : Z.Opens) ⟶ φ ⁻¹ᵁ (cU ⁻¹ᵁ V))
    (hρ : ρ.app V = a.app V ≫ b.hom.app V)
    (ha : ∀ s : M.val.obj (op (cU ⁻¹ᵁ V)), a.val.app (op V) s = M.val.map i₀.op s)
    (hb : b = (Scheme.Modules.pushforwardComp φ cU).app
            ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
          (Scheme.Modules.pushforwardCongr ht).app
              ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
          (Scheme.Modules.pushforward cW).mapIso
            ((Scheme.Modules.restrictFunctorIsoPullback φ).app M ≪≫ ι₂))
    (jU : (cU ⁻¹ᵁ V : Y.Opens) ⟶ ⊤) (jW : (cW ⁻¹ᵁ V : Z.Opens) ⟶ ⊤)
    (iT : (φ ⁻¹ᵁ (cU ⁻¹ᵁ V) : Z.Opens) ⟶ ⊤)
    (g : M.val.obj (op ⊤)) {g' : N.val.obj (op ⊤)}
    (hg : ι₂.hom.val.app (op ⊤)
      (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection φ M g) = g') :
    ρ.val.app (op V) (M.val.map jU.op g) = N.val.map jW.op g' := by
  refine Eq.trans
    (push_app_apply φ cU cW ht M N ι₂ a b ρ V i₀ i hρ ha hb (M.val.map jU.op g)) ?_
  refine Eq.trans
    (app_map_congr ι₂.hom i (pullbackSection_map φ M (cU ⁻¹ᵁ V) jU iT g)) ?_
  exact app_map_map_of ι₂.hom iT i jW _ hg

/-- **The nested comparison on the restriction of a global section, in the spelling of the
direct image.** `push_app_apply_of` with both restriction maps taken in the pushed-forward
sheaves on the ambient scheme rather than in the chart modules, which is the spelling
`Stacks.AlgebraicGeometry.ChartTransNonNested.pushforwardVal` — and therefore
`cmpNested` — uses. The two differ by `pushforward_map_eq`, applied here, at the level of
variables; applied at the concrete instance it exhausts the recursion limit. -/
public theorem push_app_apply_top (φ : Z ⟶ Y) [IsOpenImmersion φ] (cU : Y ⟶ X) (cW : Z ⟶ X)
    (ht : φ ≫ cU = cW) (M : Y.Modules) (N : Z.Modules)
    (ι₂ : (Scheme.Modules.pullback φ).obj M ≅ N)
    (a : (Scheme.Modules.pushforward cU).obj M ⟶
      (Scheme.Modules.pushforward cU).obj
        ((Scheme.Modules.pushforward φ).obj ((Scheme.Modules.restrictFunctor φ).obj M)))
    (b : (Scheme.Modules.pushforward cU).obj
          ((Scheme.Modules.pushforward φ).obj ((Scheme.Modules.restrictFunctor φ).obj M)) ≅
      (Scheme.Modules.pushforward cW).obj N)
    (ρ : (Scheme.Modules.pushforward cU).obj M ⟶ (Scheme.Modules.pushforward cW).obj N)
    (V : X.Opens)
    (i₀ : (φ ''ᵁ (φ ⁻¹ᵁ (cU ⁻¹ᵁ V)) : Y.Opens) ⟶ cU ⁻¹ᵁ V)
    (i : (cW ⁻¹ᵁ V : Z.Opens) ⟶ φ ⁻¹ᵁ (cU ⁻¹ᵁ V))
    (hρ : ρ.app V = a.app V ≫ b.hom.app V)
    (ha : ∀ s : M.val.obj (op (cU ⁻¹ᵁ V)), a.val.app (op V) s = M.val.map i₀.op s)
    (hb : b = (Scheme.Modules.pushforwardComp φ cU).app
            ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
          (Scheme.Modules.pushforwardCongr ht).app
              ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
          (Scheme.Modules.pushforward cW).mapIso
            ((Scheme.Modules.restrictFunctorIsoPullback φ).app M ≪≫ ι₂))
    (jV : V ⟶ (⊤ : X.Opens))
    (g : ((Scheme.Modules.pushforward cU).obj M).val.obj (op ⊤))
    {g' : ((Scheme.Modules.pushforward cW).obj N).val.obj (op ⊤)}
    (hg : ι₂.hom.val.app (op ⊤)
      (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection φ M g) = g') :
    ρ.val.app (op V)
        (((Scheme.Modules.pushforward cU).obj M).val.map jV.op g) =
      ((Scheme.Modules.pushforward cW).obj N).val.map jV.op g' := by
  refine Eq.trans (congrArg (ρ.val.app (op V))
    (pushforward_map_eq cU M jV (homOfLE le_top) g)) ?_
  refine Eq.trans (push_app_apply_of φ cU cW ht M N ι₂ a b ρ V i₀ i hρ ha hb
    (homOfLE le_top) (homOfLE le_top) (homOfLE le_top) g hg) ?_
  exact (pushforward_map_eq cW N jV (homOfLE le_top) g').symm

/-- **The nested comparison read as a local isomorphism, on the restriction of a global
section.** `push_app_apply_top` with the morphism replaced by any
`TopCat.Sheaf.LocalModuleEquiv` whose components it computes — which is what
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpNested` is, by `cmpNested_app`.

The `Eq.trans` that joins the two is performed here, where `e` and `ρ` are variables. Performed
at the concrete instance — joining `cmpNested_app` to `push_app_apply_top` by `Eq.trans`
in the proof of the theorem below — it exhausts the recursion limit, even with the result left
unascribed. That junction is the last of the four this file had to move into the generic
layer. -/
public theorem push_app_apply_cmp (φ : Z ⟶ Y) [IsOpenImmersion φ] (cU : Y ⟶ X) (cW : Z ⟶ X)
    (ht : φ ≫ cU = cW) (M : Y.Modules) (N : Z.Modules)
    (ι₂ : (Scheme.Modules.pullback φ).obj M ≅ N)
    (a : (Scheme.Modules.pushforward cU).obj M ⟶
      (Scheme.Modules.pushforward cU).obj
        ((Scheme.Modules.pushforward φ).obj ((Scheme.Modules.restrictFunctor φ).obj M)))
    (b : (Scheme.Modules.pushforward cU).obj
          ((Scheme.Modules.pushforward φ).obj ((Scheme.Modules.restrictFunctor φ).obj M)) ≅
      (Scheme.Modules.pushforward cW).obj N)
    (ρ : (Scheme.Modules.pushforward cU).obj M ⟶ (Scheme.Modules.pushforward cW).obj N)
    (W₀ : X.Opens)
    (e : TopCat.Sheaf.LocalModuleEquiv ((Scheme.Modules.pushforward cU).obj M).val
      ((Scheme.Modules.pushforward cW).obj N).val W₀)
    (he : ∀ (V : X.Opens) (hV : V ≤ W₀)
      (s : ((Scheme.Modules.pushforward cU).obj M).val.obj (op V)),
      e.app V hV s = ρ.val.app (op V) s)
    (V : X.Opens) (hV : V ≤ W₀)
    (i₀ : (φ ''ᵁ (φ ⁻¹ᵁ (cU ⁻¹ᵁ V)) : Y.Opens) ⟶ cU ⁻¹ᵁ V)
    (i : (cW ⁻¹ᵁ V : Z.Opens) ⟶ φ ⁻¹ᵁ (cU ⁻¹ᵁ V))
    (hρ : ρ.app V = a.app V ≫ b.hom.app V)
    (ha : ∀ s : M.val.obj (op (cU ⁻¹ᵁ V)), a.val.app (op V) s = M.val.map i₀.op s)
    (hb : b = (Scheme.Modules.pushforwardComp φ cU).app
            ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
          (Scheme.Modules.pushforwardCongr ht).app
              ((Scheme.Modules.restrictFunctor φ).obj M) ≪≫
          (Scheme.Modules.pushforward cW).mapIso
            ((Scheme.Modules.restrictFunctorIsoPullback φ).app M ≪≫ ι₂))
    (jV : V ⟶ (⊤ : X.Opens))
    (g : ((Scheme.Modules.pushforward cU).obj M).val.obj (op ⊤))
    {g' : ((Scheme.Modules.pushforward cW).obj N).val.obj (op ⊤)}
    (hg : ι₂.hom.val.app (op ⊤)
      (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection φ M g) = g') :
    e.app V hV (((Scheme.Modules.pushforward cU).obj M).val.map jV.op g) =
      ((Scheme.Modules.pushforward cW).obj N).val.map jV.op g' :=
  (he V hV _).trans
    (push_app_apply_top φ cU cW ht M N ι₂ a b ρ V i₀ i hρ ha hb jV g hg)

end Push


/-! ### The comparison for a nested pair of affine opens, on a homogeneous global section -/

section Concrete

open Stacks.AlgebraicGeometry.ProjInclusionTwist
open Stacks.AlgebraicGeometry.PullbackUnit

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (W U : S.Opens) (h : W ≤ U)
  (hW : IsAffineOpen W) (hU : IsAffineOpen U)

/-- The unit factor of the comparison is a restriction map on sections: over `V`, the restriction
from the preimage of `V` in the chart of `U` to the image of its preimage in the chart of `W`.

This is the only form of that identification the kernel will check. Identifying
`pushNestedUnit` with the pushforward of `(restrictAdjunction _).unit.app _` — which is its
definition — exceeds the kernel's deterministic timeout; identifying it with the restriction map
that unit *is* costs three seconds. See `restrictUnit_app'`. -/
public theorem pushNestedUnit_app_apply (n : ℤ) (V : (relativeProj A).scheme.Opens)
    (i₀ : (projInclusionMap A W U h hW hU ''ᵁ
        (projInclusionMap A W U h hW hU ⁻¹ᵁ ((relativeProj A).chart U hU ⁻¹ᵁ V))) ⟶
      ((relativeProj A).chart U hU ⁻¹ᵁ V))
    (s : (pushforwardVal ((relativeProj A).chart U hU)
      (twistingSheaf (A.grading U) n)).obj (op V)) :
    (pushNestedUnit A W U h hW hU n).val.app (op V) s =
      (twistingSheaf (A.grading U) n).val.map i₀.op s :=
  rfl

/-- The three tail factors of the comparison, spelled out. -/
public theorem pushNestedTail_eq (n : ℤ) :
    pushNestedTail A W U h hW hU n =
      (Scheme.Modules.pushforwardComp (projInclusionMap A W U h hW hU)
            ((relativeProj A).chart U hU)).app
          ((Scheme.Modules.restrictFunctor (projInclusionMap A W U h hW hU)).obj
            (twistingSheaf (A.grading U) n)) ≪≫
        (Scheme.Modules.pushforwardCongr
              ((relativeProj A).chart_transition W U h hW hU)).app
            ((Scheme.Modules.restrictFunctor (projInclusionMap A W U h hW hU)).obj
              (twistingSheaf (A.grading U) n)) ≪≫
          (Scheme.Modules.pushforward ((relativeProj A).chart W hW)).mapIso
            ((Scheme.Modules.restrictFunctorIsoPullback
                  (projInclusionMap A W U h hW hU)).app
                (twistingSheaf (A.grading U) n) ≪≫
              projInclusionTwistIso A W U h hW hU n) :=
  rfl

/-- The preimage of an open of the relative Proj in the chart of the smaller affine open is the
preimage, along the transition morphism, of its preimage in the chart of the larger one. This is
the chart compatibility read on opens. -/
public theorem preimage_chart_eq (V : (relativeProj A).scheme.Opens) :
    ((relativeProj A).chart W hW ⁻¹ᵁ V) =
      projInclusionMap A W U h hW hU ⁻¹ᵁ ((relativeProj A).chart U hU ⁻¹ᵁ V) :=
  (congrArg
    (fun f : AlgebraicGeometry.Proj (A.grading W) ⟶ (relativeProj A).scheme => f ⁻¹ᵁ V)
    ((relativeProj A).chart_transition W U h hW hU)).symm

/-- `Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.projInclusionTwistMap_degreeSection`
read on the isomorphism rather than on its underlying morphism. -/
public theorem projInclusionTwistIso_degreeSection (k : ℕ) (c : (A.grading U) k) :
    (projInclusionTwistIso A W U h hW hU (k : ℤ)).hom.val.app (op ⊤)
        (pullbackSection (projInclusionMap A W U h hW hU)
          (twistingSheaf (A.grading U) (k : ℤ)) (degreeSection (A.grading U) k c)) =
      degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩ :=
  (congrArg
      (fun ψ : (Scheme.Modules.pullback (projInclusionMap A W U h hW hU)).obj
            (twistingSheaf (A.grading U) (k : ℤ)) ⟶ twistingSheaf (A.grading W) (k : ℤ) =>
        ψ.val.app (op ⊤)
          (pullbackSection (projInclusionMap A W U h hW hU)
            (twistingSheaf (A.grading U) (k : ℤ)) (degreeSection (A.grading U) k c)))
      (projInclusionTwistIso_hom A W U h hW hU (k : ℤ))).trans
    (Stacks.AlgebraicGeometry.ProjInclusionDegreeSection.projInclusionTwistMap_degreeSection
      A W U h hW hU k c)

/-- **The owed section computation.** For affine opens `W ⊆ U` of the base, a degree `k` and a
homogeneous element `c` of degree `k` of the graded ring of sections over `U`, the component of
`cmpNested A W U h hW hU k` on the sections over an open `V` inside the inverse image of `W`
carries the restriction of the direct image of `degreeSection (A.grading U) k c` to the
restriction of the direct image of `degreeSection (A.grading W) k ⟨A.res h c, _⟩`.

Both restriction maps are taken in the direct images on the relative Proj, from `⊤` down to `V`,
which is the spelling in which the statement is literally "the restriction of the direct image".
The restriction morphism `jV` is a free argument: morphisms between opens are unique.

The proof is a single application: every step, including the four junctions, is assembled in
`push_app_apply_cmp` where every ingredient is a variable. Each of those
junctions performed at this instance instead — naming an intermediate result in a theorem of its
own, spelling the restriction maps in the chart modules rather than in the direct images, or
joining `cmpNested_app` to the computation by `Eq.trans` — exhausts the recursion limit or the
kernel's deterministic timeout. -/
public theorem cmpNested_degreeSection (k : ℕ) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (jV : V ⟶ (⊤ : (relativeProj A).scheme.Opens)) (c : (A.grading U) k) :
    (cmpNested A W U h hW hU (k : ℤ)).app V hV
        ((((Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
            (twistingSheaf (A.grading U) (k : ℤ))).val.map jV.op)
          (degreeSection (A.grading U) k c))
      = (((Scheme.Modules.pushforward ((relativeProj A).chart W hW)).obj
            (twistingSheaf (A.grading W) (k : ℤ))).val.map jV.op)
          (degreeSection (A.grading W) k ⟨A.res h c, (A.res h).map_mem c.2⟩) :=
  push_app_apply_cmp (projInclusionMap A W U h hW hU)
    ((relativeProj A).chart U hU) ((relativeProj A).chart W hW)
    ((relativeProj A).chart_transition W U h hW hU)
    (twistingSheaf (A.grading U) (k : ℤ)) (twistingSheaf (A.grading W) (k : ℤ))
    (projInclusionTwistIso A W U h hW hU (k : ℤ)) (pushNestedUnit A W U h hW hU (k : ℤ))
    (pushNestedTail A W U h hW hU (k : ℤ)) (pushNested A W U h hW hU (k : ℤ))
    ((relativeProj A).toBase ⁻¹ᵁ W) (cmpNested A W U h hW hU (k : ℤ))
    (cmpNested_app A W U h hW hU (k : ℤ)) V hV
    (homOfLE (Scheme.Hom.image_preimage_le _ _))
    (homOfLE (le_of_eq (preimage_chart_eq A W U h hW hU V)))
    (pushNested_app A W U h hW hU (k : ℤ) V)
    (pushNestedUnit_app_apply A W U h hW hU (k : ℤ) V
      (homOfLE (Scheme.Hom.image_preimage_le _ _)))
    (pushNestedTail_eq A W U h hW hU (k : ℤ)) jV
    (degreeSection (A.grading U) k c)
    (projInclusionTwistIso_degreeSection A W U h hW hU k c)

end Concrete

/-! ### The nested cocycle on the homogeneous global sections -/

section Cocycle

open Stacks.AlgebraicGeometry.ProjInclusionTwist
open Stacks.AlgebraicGeometry.PullbackUnit

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-- Restriction of the graded rings of sections is functorial, read on a homogeneous element.
The containment `W ≤ U` is a free argument; it agrees with the composite of the other two by
proof irrelevance. -/
public theorem res_res (W W' U : S.Opens) (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U) (k : ℕ)
    (c : (A.grading U) k) :
    (⟨A.res hWW' (⟨A.res hW'U c, (A.res hW'U).map_mem c.2⟩ : (A.grading W') k),
        (A.res hWW').map_mem
          (⟨A.res hW'U c, (A.res hW'U).map_mem c.2⟩ : (A.grading W') k).2⟩ :
        (A.grading W) k)
      = ⟨A.res hWU c, (A.res hWU).map_mem c.2⟩ := by
  refine Subtype.ext ?_
  change A.resRingHom hWW' (A.resRingHom hW'U (c : A.sectionRing U)) = A.resRingHom hWU c
  rw [← RingHom.comp_apply, ← A.resRingHom_comp]

/-- **The nested cocycle, on the homogeneous global sections.** For affine opens
`W ⊆ W' ⊆ U` of the base, a degree `k` and a homogeneous element `c` of degree `k` of the graded
ring of sections over `U`, the comparison of the chart of `U` with the chart of `W'` followed by
the comparison of the chart of `W'` with that of `W` agrees with the direct comparison of the
chart of `U` with that of `W`, on the restriction of the direct image of
`degreeSection (A.grading U) k c`.

This is `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` restricted to the
homogeneous global sections of the chart of `U`, in every degree; it is the input a rigidity
argument consumes, and it follows from `cmpNested_degreeSection` applied to each of the
three legs together with functoriality of restriction. -/
public theorem cmpNested_degreeSection_comp (k : ℕ) (W W' U : S.Opens)
    (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U)
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hU : IsAffineOpen U)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (hV' : V ≤ (relativeProj A).toBase ⁻¹ᵁ W')
    (jV : V ⟶ (⊤ : (relativeProj A).scheme.Opens)) (c : (A.grading U) k) :
    (cmpNested A W W' hWW' hW hW' (k : ℤ)).app V hV
        ((cmpNested A W' U hW'U hW' hU (k : ℤ)).app V hV'
          ((((Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
              (twistingSheaf (A.grading U) (k : ℤ))).val.map jV.op)
            (degreeSection (A.grading U) k c)))
      = (cmpNested A W U hWU hW hU (k : ℤ)).app V hV
          ((((Scheme.Modules.pushforward ((relativeProj A).chart U hU)).obj
              (twistingSheaf (A.grading U) (k : ℤ))).val.map jV.op)
            (degreeSection (A.grading U) k c)) := by
  refine Eq.trans (app_congr_arg (cmpNested A W W' hWW' hW hW' (k : ℤ)) hV
    (cmpNested_degreeSection A W' U hW'U hW' hU k V hV' jV c)) ?_
  refine Eq.trans (cmpNested_degreeSection A W W' hWW' hW hW' k V hV jV
    ⟨A.res hW'U c, (A.res hW'U).map_mem c.2⟩) ?_
  refine Eq.trans (map_congr jV (congrArg (degreeSection (A.grading W) k)
    (res_res A W W' U hWW' hW'U hWU k c))) ?_
  exact (cmpNested_degreeSection A W U hWU hW hU k V hV jV c).symm

end Cocycle

end Stacks.AlgebraicGeometry.ChartTransRelativeProj
