module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable
import StacksCore.Tactic.StacksAttribute

/-!
# Duality is exact on short exact sequences of finite locally free modules

Let `X` be a scheme and let `0 → ℰ → ℱ → 𝒢 → 0` be a short exact sequence of finite locally
free `𝒪_X`-modules. Then the dual sequence

`0 → 𝒢^∨ → ℱ^∨ → ℰ^∨ → 0`

is again short exact, where the dual of a morphism is precomposition with it. Only the right-hand
zero has content: left exactness of duality holds for any right exact sequence, while surjectivity
of `ℱ^∨ ⟶ ℰ^∨` holds because a short exact sequence of finite locally free modules splits
locally, and so splits at every stalk.

The argument is stalkwise. At a point `x` the sequence of stalks is a short exact sequence of
modules over the local ring `𝒪_{X,x}`, and the stalk of `𝒢` is free, hence projective; so the
stalk sequence splits, and a retraction `r` of `ℰ_x ⟶ ℱ_x` produces, for every functional
`ψ` on `ℰ_x`, the functional `ψ ∘ r` on `ℱ_x` restricting to it. Tag 01CP identifies the stalk of
a dual with the dual of the stalk, so that this is exactly surjectivity of `ℱ^∨_x ⟶ ℰ^∨_x`.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.injective_stalkHom`,
  `surjective_stalkHom` and `epi_of_surjective_stalkHom`: monomorphy and epimorphy of a morphism
  of `𝒪_X`-modules, read on stalks in the `stalkHom` vocabulary.
* `Stacks.AlgebraicGeometry.ReflexiveModules.exists_stalkHom_eq_of_exact`: exactness of a short
  complex at a stalk, in element form.
* `Stacks.AlgebraicGeometry.ReflexiveModules.stalkShortComplex_shortExact`: the sequence of
  stalks of a short exact sequence of `𝒪_X`-modules is short exact.
* `Stacks.AlgebraicGeometry.ReflexiveModules.exists_stalkHom_retraction`: at every point, a short
  exact sequence whose last term is finite locally free splits.
* `Stacks.AlgebraicGeometry.ReflexiveModules.epi_dualMap_of_shortExact`: **the dual of the
  monomorphism of a short exact sequence of finite locally free modules is an epimorphism.**
* `Stacks.AlgebraicGeometry.ReflexiveModules.exists_dualSheaf_shortExact`: the dual sequence of a
  short exact sequence of finite locally free modules is short exact.

## Implementation notes

The stalkwise criteria of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/StalkwiseExactness.lean` are stated for the stalk
functor into modules over the `RingCat`-valued stalk of the sheaf of rings, while the stalk of a
dual is computed by Tag 01CP over the `CommRingCat`-valued stalk, i.e. over the local ring
`𝒪_{X,x}`; those are two different filtered colimits. Only the *underlying functions* of the two
stalk maps are needed here, and they agree, which is `stalkMap_apply_eq_stalkHom`: both send the
germ of a local section to the germ of its image. The criteria are therefore restated once, in
the `stalkHom` vocabulary over the local ring, and everything downstream stays on that side.

Exactness of the stalk sequence is read off in element form rather than transported as a short
complex, since `ShortComplex.map` would require the preservation instances of the stalk functor
at the `AlgebraicGeometry.Scheme.Modules` spelling of the category of `𝒪_X`-modules, where they
are not found: that spelling is a `def` with its own `Hom` and its own `Category` instance, so
an instance registered for `CategoryTheory.SheafOfModules X.ringCatSheaf` does not match it.
The hypotheses and conclusions here are written at the `Scheme.Modules` spelling, which is the
one the dual sheaf and its stalk comparison are written at, and the crossing to the other
spelling happens only inside the proofs, where it is a unification and not an instance search.

The left exactness of duality is taken from Tag 0GMY in its ringed-site form, at the ringed site
`schemeRingedSite X` of the opens of `X`: the dual of a morphism, `dualMap`, is precomposition in
the first variable of the internal Hom sheaf, which is what that tag is stated about, and the two
constructions are the same term.

## References

* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-! ### Stalkwise criteria over the local ring -/

/-- The stalk map of a morphism of `𝒪_X`-modules, as produced by the stalk functor into modules
over the `RingCat`-valued stalk of the sheaf of rings, has `stalkHom` as its underlying function:
both send the germ of a local section to the germ of its image. -/
theorem stalkMap_apply_eq_stalkHom {E F : X.Modules} (f : E ⟶ F) (x : X) (m : modStalk E x) :
    (AlgebraicGeometry.SheafOfModules.stalkMap (structureSheaf X.sheaf) x f).hom m
      = stalkHom f x m := by
  obtain ⟨W, hxW, t, rfl⟩ := exists_germ_eq E m
  rw [stalkHom_germAt f x W hxW t]
  exact AlgebraicGeometry.SheafOfModules.stalkMap_germ (structureSheaf X.sheaf) x f W hxW t

/-- `stalkMap_apply_eq_stalkHom` as an equality of functions. -/
private theorem coe_stalkMap_hom_eq_stalkHom {E F : X.Modules} (f : E ⟶ F) (x : X) :
    ⇑(AlgebraicGeometry.SheafOfModules.stalkMap (structureSheaf X.sheaf) x f).hom
      = stalkHom f x :=
  funext (stalkMap_apply_eq_stalkHom f x)

/-- **A monomorphism of `𝒪_X`-modules is injective on stalks.** -/
theorem injective_stalkHom {E F : X.Modules} (f : E ⟶ F) (hf : Mono f) (x : X) :
    Function.Injective (stalkHom f x) := by
  have := (AlgebraicGeometry.SheafOfModules.mono_iff_injective_stalkMap
    (O := structureSheaf X.sheaf) f).1 hf x
  rwa [coe_stalkMap_hom_eq_stalkHom] at this

/-- **An epimorphism of `𝒪_X`-modules is surjective on stalks.** -/
theorem surjective_stalkHom {E F : X.Modules} (f : E ⟶ F) (hf : Epi f) (x : X) :
    Function.Surjective (stalkHom f x) := by
  have := (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
    (O := structureSheaf X.sheaf) f).1 hf x
  rwa [coe_stalkMap_hom_eq_stalkHom] at this

/-- **A morphism of `𝒪_X`-modules which is surjective on every stalk is an epimorphism.** -/
theorem epi_of_surjective_stalkHom {E F : X.Modules} (f : E ⟶ F)
    (h : ∀ x : X, Function.Surjective (stalkHom f x)) : Epi f := by
  refine (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
    (O := structureSheaf X.sheaf) f).2 fun x => ?_
  rw [coe_stalkMap_hom_eq_stalkHom]
  exact h x

/-- **Exactness at a stalk, in element form.** An element of the stalk of the middle term of an
exact short complex which is killed by the second map is the image of an element of the stalk of
the first term. -/
theorem exists_stalkHom_eq_of_exact {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0) (hex : (ShortComplex.mk f g w).Exact) (x : X) (m : modStalk F x)
    (hm : stalkHom g x m = 0) : ∃ a : modStalk E x, stalkHom f x a = m := by
  have hex' :
      (ShortComplex.mk (C := _root_.SheafOfModules.{u} (structureSheaf X.sheaf)) f g w).Exact :=
    hex
  have h := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact _).1 hex' x
  rw [ShortComplex.moduleCat_exact_iff] at h
  obtain ⟨a, ha⟩ := h m ((stalkMap_apply_eq_stalkHom g x m).trans hm)
  exact ⟨a, (stalkMap_apply_eq_stalkHom f x a).symm.trans ha⟩

/-- The zero morphism of `𝒪_X`-modules induces the zero map on stalks. -/
theorem stalkHom_zero {E F : X.Modules} (x : X) : stalkHom (0 : E ⟶ F) x = 0 := by
  refine linearMap_ext fun W hxW t => (stalkHom_germAt (0 : E ⟶ F) x W hxW t).trans ?_
  exact (congrArg (germAt F W x hxW)
    (show Scheme.Modules.Hom.app (0 : E ⟶ F) W t = 0 from rfl)).trans (germAt_zero F hxW)

/-! ### The sequence of stalks -/

/-- The short complex of stalks at a point of a short complex of `𝒪_X`-modules, as a short
complex of modules over the local ring at that point. -/
noncomputable def stalkShortComplex {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0) (x : X) : ShortComplex (ModuleCat.{u} (ringStalk X.sheaf x)) where
  X₁ := ModuleCat.of _ (modStalk E x)
  X₂ := ModuleCat.of _ (modStalk F x)
  X₃ := ModuleCat.of _ (modStalk G x)
  f := ModuleCat.ofHom (stalkHom f x)
  g := ModuleCat.ofHom (stalkHom g x)
  zero := by
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun a => ?_
    have h : (stalkHom g x).comp (stalkHom f x) = 0 := by
      rw [← stalkHom_comp f g x, w, stalkHom_zero]
    exact LinearMap.congr_fun h a

/-- **The sequence of stalks of a short exact sequence of `𝒪_X`-modules is short exact.** -/
theorem stalkShortComplex_shortExact {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0) (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact)
    (x : X) : (stalkShortComplex f g w x).ShortExact where
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro m hm
    exact exists_stalkHom_eq_of_exact f g w hex x m hm
  mono_f := (ModuleCat.mono_iff_injective _).2 (injective_stalkHom f hmono x)
  epi_g := (ModuleCat.epi_iff_surjective _).2 (surjective_stalkHom g hepi x)

/-- **A short exact sequence of `𝒪_X`-modules whose last term is finite locally free splits at
every stalk.** The stalk of a finite locally free module is a free, hence projective, module over
the local ring, so the sequence of stalks admits a retraction of its first map. -/
theorem exists_stalkHom_retraction {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0) (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact)
    (hG : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (x : X) :
    ∃ r : F.presheaf.stalk x →ₗ[X.presheaf.stalk x] E.presheaf.stalk x,
      ∀ a : modStalk E x, r (stalkHom f x a) = a := by
  have := hG
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) G :=
    Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree G
  have : Module.Free (ringStalk X.sheaf x) (modStalk G x) :=
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree G x).1
  have : CategoryTheory.Projective (stalkShortComplex f g w x).X₃ :=
    inferInstanceAs (CategoryTheory.Projective
      (ModuleCat.of (ringStalk X.sheaf x) (modStalk G x)))
  let sp := (stalkShortComplex_shortExact f g w hmono hepi hex x).splittingOfProjective
  refine ⟨sp.r.hom, fun a => ?_⟩
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom sp.f_r) a

/-! ### The dual sequence -/

/-- Germs over a common open neighbourhood: two elements of the stalks at `x` of two
`𝒪_X`-modules are the germs of sections over one and the same neighbourhood of `x`. -/
theorem exists_germ_eq_pair (M N : X.Modules) {x : X} (m : modStalk M x) (n : modStalk N x) :
    ∃ (W : X.Opens) (hx : x ∈ W) (t : Γ(M, W)) (s : Γ(N, W)),
      germAt M W x hx t = m ∧ germAt N W x hx s = n := by
  obtain ⟨W₁, hx₁, t, ht⟩ := exists_germ_eq M m
  obtain ⟨W₂, hx₂, s, hs⟩ := exists_germ_eq N n
  refine ⟨W₁ ⊓ W₂, ⟨hx₁, hx₂⟩, resLE M inf_le_left t, resLE N inf_le_right s, ?_, ?_⟩
  · exact (germAt_resLE M inf_le_left (⟨hx₁, hx₂⟩ : x ∈ W₁ ⊓ W₂) t).trans ht
  · exact (germAt_resLE N inf_le_right (⟨hx₁, hx₂⟩ : x ∈ W₁ ⊓ W₂) s).trans hs

/-- **The dual of a morphism is precomposition, at every stalk.** Under the identification of the
stalk of a dual with the dual of the stalk of Tag 01CP, the dual `dualMap f` of a morphism
`f : ℰ ⟶ ℱ` induces precomposition with the stalk map of `f`. -/
theorem dualStalkEquiv_stalkHom_dualMap {E F : X.Modules} [E.IsFinitePresentation]
    [F.IsFinitePresentation] (f : E ⟶ F) (x : X) (φ : modStalk (dualSheaf F) x)
    (m : modStalk E x) :
    dualStalkEquiv E x (stalkHom (dualMap f) x φ) m
      = dualStalkEquiv F x φ (stalkHom f x m) := by
  obtain ⟨W, hxW, t, s, rfl, rfl⟩ := exists_germ_eq_pair (dualSheaf F) E φ m
  refine (congrArg (fun z => dualStalkEquiv E x z (germAt E W x hxW s))
    (stalkHom_germAt (dualMap f) x W hxW t)).trans ?_
  refine ((dualStalkEquiv_germ E x W hxW (Scheme.Modules.Hom.app (dualMap f) W t) s).trans ?_).trans
    (congrArg (fun z => dualStalkEquiv F x (germAt (dualSheaf F) W x hxW t) z)
      (stalkHom_germAt f x W hxW s).symm)
  exact (congrArg (X.presheaf.germ W x hxW)
      (dualPairing_dualMap f t (Over.mk (𝟙 W)) s)).trans
    (dualStalkEquiv_germ F x W hxW t (Scheme.Modules.Hom.app f W s)).symm

/-- **The dual of the monomorphism of a short exact sequence of finite locally free modules is an
epimorphism.** This is the half of the exactness of duality with content: the sequence splits at
every stalk, and a functional on the stalk of `ℰ` extends to the stalk of `ℱ` along a retraction.
-/
theorem epi_dualMap_of_shortExact {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0) (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact)
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G) :
    Epi (dualMap f) := by
  have := hE
  have := hF
  have : E.IsFinitePresentation := Stacks.FiniteLocallyFree.isFinitePresentation E
  have : F.IsFinitePresentation := Stacks.FiniteLocallyFree.isFinitePresentation F
  refine epi_of_surjective_stalkHom (dualMap f) fun x ψ => ?_
  obtain ⟨r, hr⟩ := exists_stalkHom_retraction f g w hmono hepi hex hG x
  refine ⟨(dualStalkEquiv F x).symm ((dualStalkEquiv E x ψ).comp r), ?_⟩
  refine (dualStalkEquiv E x).injective (LinearMap.ext fun m => ?_)
  have h1 := dualStalkEquiv_stalkHom_dualMap f x
    ((dualStalkEquiv F x).symm ((dualStalkEquiv E x ψ).comp r)) m
  have h2 := (dualStalkEquiv F x).apply_symm_apply ((dualStalkEquiv E x ψ).comp r)
  exact h1.trans ((LinearMap.congr_fun h2 (stalkHom f x m)).trans
    (congrArg (dualStalkEquiv E x ψ) (hr m)))

/-- **The dual of a short exact sequence of finite locally free modules is short exact**: a short
exact sequence `0 → ℰ → ℱ → 𝒢 → 0` of finite locally free `𝒪_X`-modules gives rise to a short
exact sequence `0 → 𝒢^∨ → ℱ^∨ → ℰ^∨ → 0`, whose morphisms are the duals of the given ones.

Monomorphy of `𝒢^∨ ⟶ ℱ^∨` and exactness at `ℱ^∨` are Tag 0GMY, which needs only that
`ℱ ⟶ 𝒢` be an epimorphism; epimorphy of `ℱ^∨ ⟶ ℰ^∨` is `epi_dualMap_of_shortExact`. -/
theorem exists_dualSheaf_shortExact {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0) (hmono : Mono f) (hepi : Epi g) (hex : (ShortComplex.mk f g w).Exact)
    (hE : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G) :
    ∃ w' : dualMap g ≫ dualMap f = 0,
      (ShortComplex.mk (dualMap g) (dualMap f) w').ShortExact := by
  have hepi' : Epi (C := _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O)) g := hepi
  obtain ⟨w', hex'⟩ :=
    Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomMapLeft_exact_of_exact_epi
      (schemeRingedSite X)
      (ShortComplex.mk (C := _root_.SheafOfModules.{u} (structureSheaf X.sheaf)) f g w)
      (SheafOfModules.unit (structureSheaf X.sheaf)) hex
  exact ⟨w', { exact := hex'
               mono_f :=
                 Stacks.SheafOfModules.InternalHom.ringedSite_sheafInternalHomMapLeft_mono_of_epi
                   (schemeRingedSite X) g
               epi_g := epi_dualMap_of_shortExact f g w hmono hepi hex hE hF hG }⟩

end Stacks.AlgebraicGeometry.ReflexiveModules

end
