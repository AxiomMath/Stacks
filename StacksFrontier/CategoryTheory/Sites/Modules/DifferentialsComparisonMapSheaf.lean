module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
import StacksCore.Tactic.EgaSgaAttribute
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison map of sheaves of differentials along a commutative square

Let
```
        f
   X' -----> X
   |         |
   v         v
   Y' -----> Y
```
be a commutative diagram of morphisms of ringed topoi. The structure map
`f♯ : O_X ⟶ f_* O_{X'}` followed by `f_* d_{X'/Y'}` is a `Y`-derivation, so the universal
property of `Ω_{X/Y}` gives a map `c'_f : Ω_{X/Y} ⟶ f_* Ω_{X'/Y'}`, and its adjoint transpose
is the comparison map `c_f : f^* Ω_{X/Y} ⟶ Ω_{X'/Y'}`, characterized by
`c_f (f^* d_{X/Y}(t)) = d_{X'/Y'}(f^* t)` for local sections `t` of `O_X`.

Here `Ω_{X/Y}` and `Ω_{X'/Y'}` are the sheaves of differentials of the source: the sheaves of
modules representing derivations into *sheaves* of modules, namely
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite` applied to the structure map
`g♯ : g⁻¹O_Y ⟶ O_X`, with universal derivation `universalDerivationOfSite`.

## Main definitions

* `Stacks.Sheaves.Differentials.RingedSiteOverBase`: a site with a sheaf of commutative rings
  `O_X` and the structure map `g♯ : g⁻¹O_Y ⟶ O_X` from the inverse image of the base.
* `Stacks.Sheaves.Differentials.RingedSiteOverBase.differentials`: the sheaf of differentials
  `Ω_{X/Y}`, with `universalDerivation` its universal `Y`-derivation `d_{X/Y}`.
* `Stacks.Sheaves.Differentials.RingedSiteOverBase.Hom`: a morphism `f : X' ⟶ X` of ringed
  topoi lying over a morphism of the bases, with the commutativity of the square.

## Main results

* `Stacks.Sheaves.Differentials.RingedSiteOverBase.Hom.comparison_differentials`: the three
  assertions of the source: the composite is a `Y`-derivation, the map `c'_f` exists and is
  unique, and `c_f` is the unique `O_{X'}`-linear map with the stated effect on the sections
  `f^* d_{X/Y}(t)`; moreover `c_f` is the adjoint transpose of `c'_f`.

## Implementation notes

A morphism of ringed topoi is given, as in
`StacksFrontier/CategoryTheory/Sites/Modules/DifferentialsComparisonMap.lean`, by a continuous
functor of the underlying sites together with the structure map of sheaves of rings, and the
pullback of modules `f^*` is the left adjoint of the pushforward of modules, which always
exists in this setting. The bottom map
`Y' ⟶ Y` of the square enters only through the map `g_X⁻¹O_Y ⟶ f_* g_{X'}⁻¹O_{Y'}` it induces,
and the commutativity of the square is the equality of the two composites to `f_* O_{X'}`.

The sheaf of differentials is the corepresenting object of derivations into sheaves of
modules on the site, which exists on an arbitrary site (the sheafification of the presheaf of
sectionwise Kähler differentials). Its universal property quantifies over sheaves of modules
only; the presheaf of sectionwise Kähler differentials is in general not a sheaf.

The sites are small categories `C : Type u` and the rings and modules live in the same
universe `u`. This is the setting in which the library constructs the pullback of modules
along a continuous functor (`Stacks.Sheaves.ModuleAdjunction.pushforward_isRightAdjoint`,
Stacks 03D7), so `f^*` and the adjunction `f^* ⊣ f_*` are supplied by that construction and
are not part of the data of a morphism. Sheafification of abelian presheaves on a small site,
which that construction uses, is provided by `siteHasSheafify` and
`siteWEqualsLocallyBijective`.

## References

* [Stacks Project, Tag 04BR](https://stacks.math.columbia.edu/tag/04BR)
* [Stacks Project, Tag 04BQ](https://stacks.math.columbia.edu/tag/04BQ)
-/

@[expose] public section

open CategoryTheory PresheafOfModules
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite universalDerivationOfSite)
open Stacks.SheafOfModules.Tensor (ringSheaf)

namespace Stacks.Sheaves.Differentials

universe u

/-- A **ringed site over a base**: a site `(C, J)` with a sheaf of commutative rings `O = O_X`
and a morphism of sheaves of commutative rings `φ : OY ⟶ O`, where `OY` stands for the inverse
image `g⁻¹O_Y` of the structure sheaf of the base and `φ` for the structure map `g♯` of the
morphism `g : X ⟶ Y` of ringed topoi. No sheaf of differentials is part of the data: it is
`RingedSiteOverBase.differentials`. -/
structure RingedSiteOverBase where
  /-- The site underlying the topos `Sh(C_X)`. -/
  {C : Type u}
  /-- The site is a small category. -/
  [cat : SmallCategory C]
  /-- The Grothendieck topology defining the topos. -/
  J : GrothendieckTopology C
  /-- The structure sheaf of commutative rings `O_X`. -/
  O : Sheaf J CommRingCat.{u}
  /-- The inverse image `g⁻¹O_Y` of the structure sheaf of the base. -/
  OY : Sheaf J CommRingCat.{u}
  /-- The structure map `g♯ : g⁻¹O_Y ⟶ O_X` of the morphism `g : X ⟶ Y`. -/
  φ : OY ⟶ O

attribute [instance] RingedSiteOverBase.cat

namespace RingedSiteOverBase

variable (X : RingedSiteOverBase.{u})

instance : X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  Stacks.hasSheafCompose_forget₂_commRingCat X.J

/-- Sheafification of abelian presheaves exists on the small site of `X`. -/
instance : HasSheafify X.J AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify

/-- On the small site of `X`, sheafification inverts exactly the locally bijective maps. -/
instance : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective

/-- The sheaf of differentials `Ω_{X/Y} = Ω_{O_X/g⁻¹O_Y}`: the sheaf of `O_X`-modules
representing `Y`-derivations into sheaves of `O_X`-modules. -/
noncomputable abbrev differentials : _root_.SheafOfModules.{u} (ringSheaf X.O) :=
  moduleOfDifferentialsOfSite.{u, u, u, u} X.OY X.O X.φ

/-- The universal `Y`-derivation `d_{X/Y} : O_X ⟶ Ω_{X/Y}`. -/
noncomputable abbrev universalDerivation :
    PresheafOfModulesOfCommRing.Derivation' X.differentials.val X.φ.hom :=
  universalDerivationOfSite.{u, u, u, u} X.OY X.O X.φ

/-- `d_{X/Y}` is universal among `Y`-derivations into sheaves of `O_X`-modules. -/
theorem existsUnique_descDerivation
    (F : _root_.SheafOfModules.{u} (ringSheaf X.O))
    (D : PresheafOfModulesOfCommRing.Derivation' F.val X.φ.hom) :
    ∃! g : X.differentials ⟶ F, X.universalDerivation.postcomp g.val = D :=
  AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation.{u, u, u, u} X.OY X.O X.φ F D

/-- A **morphism `f : X' ⟶ X` of ringed topoi over a morphism of the bases**, that is, a
commutative square
```
        f
   X' -----> X
   |         |
   v         v
   Y' -----> Y .
```
It consists of a continuous functor `Ff : C_X ⥤ C_X'` of the underlying sites, the structure
map `fsharp : O_X ⟶ f_* O_{X'}`, the map `fsharpY : g_X⁻¹O_Y ⟶ f_* g_{X'}⁻¹O_{Y'}`
induced by the bottom map `Y' ⟶ Y`, and the commutativity `hcomm` of the square of structure
sheaves. -/
structure Hom (X' X : RingedSiteOverBase.{u}) where
  /-- The underlying continuous functor of sites `C_X ⥤ C_X'`. -/
  Ff : X.C ⥤ X'.C
  /-- `Ff` is continuous for the topologies. -/
  [continuous : Ff.IsContinuous X.J X'.J]
  /-- The structure map `f♯ : O_X ⟶ f_* O_{X'}` (sheaves of rings). -/
  fsharp : ringSheaf X.O ⟶ (Ff.sheafPushforwardContinuous RingCat.{u} X.J X'.J).obj
    (ringSheaf X'.O)
  /-- The map `g_X⁻¹O_Y ⟶ f_* g_{X'}⁻¹O_{Y'}` induced by the bottom map `Y' ⟶ Y`. -/
  fsharpY : X.OY.obj ⟶ Ff.op ⋙ X'.OY.obj
  /-- Commutativity of the square of structure sheaves: the two composites
  `g_X⁻¹O_Y ⟶ f_* O_{X'}` agree. -/
  hcomm :
    Functor.whiskerRight X.φ.hom (forget₂ CommRingCat.{u} RingCat.{u}) ≫
        (sheafToPresheaf X.J RingCat.{u}).map fsharp =
      Functor.whiskerRight fsharpY (forget₂ CommRingCat.{u} RingCat.{u}) ≫
        Functor.whiskerLeft Ff.op
          (Functor.whiskerRight X'.φ.hom (forget₂ CommRingCat.{u} RingCat.{u}))

attribute [instance] Hom.continuous

namespace Hom

variable {X' X : RingedSiteOverBase.{u}} (f : Hom X' X)

/-- The pushforward `f_* Ω_{X'/Y'}`, a sheaf of `O_X`-modules via `f♯`. -/
noncomputable abbrev pushΩ : _root_.SheafOfModules.{u} (ringSheaf X.O) :=
  (_root_.SheafOfModules.pushforward.{u} f.fsharp).obj X'.differentials

/-- The pullback `f^* Ω_{X/Y}`, a sheaf of `O_{X'}`-modules. -/
noncomputable abbrev pullΩ : _root_.SheafOfModules.{u} (ringSheaf X'.O) :=
  (_root_.SheafOfModules.pullback.{u} f.fsharp).obj X.differentials

/-- The adjunction `f^* ⊣ f_*` on sheaves of modules. -/
noncomputable abbrev adj :
    _root_.SheafOfModules.pullback.{u} f.fsharp ⊣
      _root_.SheafOfModules.pushforward.{u} f.fsharp :=
  _root_.SheafOfModules.pullbackPushforwardAdjunction.{u} f.fsharp

/-- The structure map on local sections: the ring map `O_X(U) ⟶ O_{X'}(Ff U)`, so that
`f.fsharpApp U t` is the local section `f^* t`. -/
noncomputable abbrev fsharpApp (U : X.Cᵒᵖ) :
    ((ringSheaf X.O).obj.obj U) →+* ((ringSheaf X'.O).obj.obj (f.Ff.op.obj U)) :=
  (((sheafToPresheaf X.J RingCat.{u}).map f.fsharp).app U).hom

/-- The local section `f^* d_{X/Y}(t)` of `f^* Ω_{X/Y}` over `Ff U`, for `t ∈ O_X(U)`: the image
of `d_{X/Y}(t)` under the unit `Ω_{X/Y} ⟶ f_* f^* Ω_{X/Y}` of the adjunction. -/
noncomputable abbrev pullbackDiff (U : X.Cᵒᵖ) (t : (ringSheaf X.O).obj.obj U) :
    f.pullΩ.val.obj (f.Ff.op.obj U) :=
  (((f.adj).unit.app X.differentials).val.app U).hom (X.universalDerivation.d t)

/-- The composite `f_* d_{X'/Y'} ∘ f♯ : O_X ⟶ f_* Ω_{X'/Y'}`, `a ↦ d_{X'/Y'}(f♯ a)`, is a
`Y`-derivation. -/
theorem exists_derivation_pushforward :
    ∃ D : PresheafOfModulesOfCommRing.Derivation' f.pushΩ.val X.φ.hom,
      ∀ (U : X.Cᵒᵖ) (a : (ringSheaf X.O).obj.obj U),
        (D.app U).d a = (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U a) := by
  refine ⟨{ d := fun {U} => (AddMonoidHom.mk'
              (fun a => (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U a))
              (fun a b =>
                (congrArg (X'.universalDerivation.app (f.Ff.op.obj U)).d
                  (map_add (f.fsharpApp U) a b)).trans (map_add _ _ _)) :
                ((ringSheaf X.O).obj.obj U) →+ f.pushΩ.val.obj U)
            d_mul := ?_
            d_map := ?_
            d_app := ?_ }, ?_⟩
  · intro U a b
    exact (congrArg (X'.universalDerivation.app (f.Ff.op.obj U)).d
      (map_mul (f.fsharpApp U) a b)).trans
        ((X'.universalDerivation.app (f.Ff.op.obj U)).d_mul _ _)
  · intro U V g x
    have key : f.fsharpApp V ((ringSheaf X.O).obj.map g x)
        = (ringSheaf X'.O).obj.map (f.Ff.op.map g) (f.fsharpApp U x) :=
      congrFun (congrArg (fun φ => φ.hom)
        (((sheafToPresheaf X.J RingCat).map f.fsharp).naturality g)) x
    exact (congrArg (X'.universalDerivation.app (f.Ff.op.obj V)).d key).trans
      (X'.universalDerivation.d_map (f.Ff.op.map g) (f.fsharpApp U x))
  · intro U s
    have key : f.fsharpApp U (X.φ.hom.app U s)
        = X'.φ.hom.app (f.Ff.op.obj U) (f.fsharpY.app U s) :=
      congrArg (fun η => (η.app U).hom s) f.hcomm
    exact (congrArg (X'.universalDerivation.app (f.Ff.op.obj U)).d key).trans
      (ModuleCat.Derivation.d_map (X'.universalDerivation.app (f.Ff.op.obj U))
        (f.fsharpY.app U s))
  · exact fun _ _ => rfl

/-- For the adjoint transpose `cf'` of `cf : f^* Ω_{X/Y} ⟶ Ω_{X'/Y'}`, the value of `cf'` on
`d_{X/Y}(t)` is the value of `cf` on `f^* d_{X/Y}(t)`. -/
theorem homEquiv_apply_universalDerivation (cf : f.pullΩ ⟶ X'.differentials)
    (U : X.Cᵒᵖ) (t : (ringSheaf X.O).obj.obj U) :
    ((((f.adj).homEquiv X.differentials X'.differentials cf).val.app U).hom
        (X.universalDerivation.d t))
      = (cf.val.app (f.Ff.op.obj U)).hom (f.pullbackDiff U t) := by
  rw [Adjunction.homEquiv_unit]
  change (((_root_.SheafOfModules.pushforward f.fsharp).map cf).val.app U).hom
      (((f.adj.unit.app X.differentials).val.app U).hom (X.universalDerivation.d t))
    = (cf.val.app (f.Ff.op.obj U)).hom (f.pullbackDiff U t)
  rw [_root_.SheafOfModules.pushforward_map_val]
  exact PresheafOfModules.pushforward_map_app_apply f.fsharp.hom cf.val U _

/-- The map `c'_f : Ω_{X/Y} ⟶ f_* Ω_{X'/Y'}` with `c'_f(d_{X/Y} t) = d_{X'/Y'}(f♯ t)` exists
and is unique. -/
theorem existsUnique_comparisonTranspose :
    ∃! cf' : X.differentials ⟶ f.pushΩ,
      ∀ (U : X.Cᵒᵖ) (t : (ringSheaf X.O).obj.obj U),
        (cf'.val.app U).hom (X.universalDerivation.d t)
          = (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U t) := by
  obtain ⟨D, hD⟩ := f.exists_derivation_pushforward
  have iff : ∀ cf' : X.differentials ⟶ f.pushΩ,
      (∀ (U : X.Cᵒᵖ) (t : (ringSheaf X.O).obj.obj U),
        (cf'.val.app U).hom (X.universalDerivation.d t)
          = (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U t)) ↔
        X.universalDerivation.postcomp cf'.val = D := by
    intro cf'
    refine ⟨fun h => ?_, fun h U t => ?_⟩
    · apply PresheafOfModulesOfCommRing.Derivation.ext
      funext U
      apply AddMonoidHom.ext
      intro t
      change (cf'.val.app U).hom (X.universalDerivation.d t) = D.d t
      rw [h U t]
      exact (hD U t).symm
    · change (X.universalDerivation.postcomp cf'.val).d t = _
      rw [h]
      exact hD U t
  obtain ⟨cf', hcf', huniq⟩ := X.existsUnique_descDerivation f.pushΩ D
  exact ⟨cf', (iff cf').2 hcf', fun g hg => huniq g ((iff g).1 hg)⟩

/-- **Stacks 04BR.** For a commutative square of morphisms of ringed topoi, `f : X' ⟶ X` over
`Y' ⟶ Y`:

1. the composite `f_* d_{X'/Y'} ∘ f♯ : O_X ⟶ f_* Ω_{X'/Y'}`, `a ↦ d_{X'/Y'}(f♯ a)`, is a
   `Y`-derivation;
2. hence there is a unique `O_X`-linear map `c'_f : Ω_{X/Y} ⟶ f_* Ω_{X'/Y'}` with
   `c'_f(d_{X/Y} t) = d_{X'/Y'}(f♯ t)` for every local section `t`;
3. the comparison map `c_f : f^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` is the unique `O_{X'}`-linear map sending
   `f^* d_{X/Y}(t)` to `d_{X'/Y'}(f^* t)` for every local section `t` of `O_X`;
4. and this `c_f` is the map obtained from `c'_f` by the adjunction `f^* ⊣ f_*`.

Here `Ω_{X/Y}` and `Ω_{X'/Y'}` are the sheaves of differentials of Stacks 04BQ, universal among
derivations into sheaves of modules. A local section `t ∈ O_X(U)` is pulled back to the section
`f♯ t` over `Ff U`, and `f^* d_{X/Y}(t)` is the image of `d_{X/Y}(t)` under the unit of the
adjunction, a section of `f^* Ω_{X/Y}` over `Ff U` (`pullbackDiff`); the source's equation of
maps out of `f⁻¹h_U^#` is the equation of these sections. -/
@[stacks 04BR, ega "0 20.5.2" "(20.5.2.4) & (20.5.2.6)", ega "IV 16.4.3" "(16.4.3.6),(16.4.3.7)"]
theorem comparison_differentials :
    (∃ D : PresheafOfModulesOfCommRing.Derivation' f.pushΩ.val X.φ.hom,
      ∀ (U : X.Cᵒᵖ) (a : (ringSheaf X.O).obj.obj U),
        (D.app U).d a = (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U a)) ∧
    (∃! cf' : X.differentials ⟶ f.pushΩ,
      ∀ (U : X.Cᵒᵖ) (t : (ringSheaf X.O).obj.obj U),
        (cf'.val.app U).hom (X.universalDerivation.d t)
          = (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U t)) ∧
    (∃! cf : f.pullΩ ⟶ X'.differentials,
      ∀ (U : X.Cᵒᵖ) (t : (ringSheaf X.O).obj.obj U),
        (cf.val.app (f.Ff.op.obj U)).hom (f.pullbackDiff U t)
          = (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U t)) ∧
    ∀ (cf : f.pullΩ ⟶ X'.differentials) (cf' : X.differentials ⟶ f.pushΩ),
      (∀ (U : X.Cᵒᵖ) (t : (ringSheaf X.O).obj.obj U),
        (cf'.val.app U).hom (X.universalDerivation.d t)
          = (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U t)) →
      (∀ (U : X.Cᵒᵖ) (t : (ringSheaf X.O).obj.obj U),
        (cf.val.app (f.Ff.op.obj U)).hom (f.pullbackDiff U t)
          = (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U t)) →
      (f.adj).homEquiv X.differentials X'.differentials cf = cf' := by
  obtain ⟨cf', hcf', huniq⟩ := f.existsUnique_comparisonTranspose
  set e := (f.adj).homEquiv X.differentials X'.differentials
  have transpose : ∀ cf : f.pullΩ ⟶ X'.differentials,
      (∀ (U : X.Cᵒᵖ) (t : (ringSheaf X.O).obj.obj U),
        (cf.val.app (f.Ff.op.obj U)).hom (f.pullbackDiff U t)
          = (X'.universalDerivation.app (f.Ff.op.obj U)).d (f.fsharpApp U t)) →
      e cf = cf' := fun cf hcf =>
    huniq (e cf) fun U t => (f.homEquiv_apply_universalDerivation cf U t).trans (hcf U t)
  refine ⟨f.exists_derivation_pushforward, ⟨cf', hcf', huniq⟩, ⟨e.symm cf', ?_, ?_⟩, ?_⟩
  · intro U t
    rw [← f.homEquiv_apply_universalDerivation, e.apply_symm_apply]
    exact hcf' U t
  · exact fun cg hcg => e.eq_symm_apply.2 (transpose cg hcg)
  · intro cf cg hcg hcf
    rw [transpose cf hcf, huniq cg hcg]

end Hom

end RingedSiteOverBase

end Stacks.Sheaves.Differentials

end
