module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.OpenDirectImagePullback

/-!
# The Čech base change of Tag 0G7U fails for a non-quasi-coherent module

[Stacks, Tag 0G7U] fixes `g : X' ⟶ X`, equations `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with pullbacks
`f'ᵢ = g^♯(fᵢ)`, and an *arbitrary* `𝒪_X`-module `ℱ` with `ℱ' = g^*ℱ`, and notes
"`(ℱ')^• = g^*ℱ^•`" for the extended alternating Čech complexes.  This file shows that the
note is **false** without a quasi-coherence hypothesis.  For quasi-coherent `ℱ` it holds, through
the comparison map: `Stacks.Perfect.CechBaseChange.isIso_cplxBaseChange`.

## The counterexample

Let `k` be any field, `X = 𝔸²_k = Spec k[x, y]`, `c = 1`, `f₁ = x`, so that `U = D(x)`, and let
`g : X' = 𝔸¹_k = Spec k[t] ⟶ X` be the diagonal, `x, y ↦ t`, so that `f'₁ = t` and `U' = D(t)`.
Let `ζ` be the generic point of the line `y = 0` and let `ℱ ⊆ 𝒪_X` be the sheaf of functions
whose germ at `ζ` vanishes (`coeff`).  An open `V` contains `ζ` exactly when it meets the line
`y = 0`, and `X` is integral, so `ℱ(V) = 𝒪(V)` for `V ⊆ D(y)` and `ℱ(V) = 0` otherwise: `ℱ` is
the extension by zero of `𝒪` from `D(y)`.  The degree-one terms of the two complexes are

* `g^*(j_*(ℱ|_U))`: for every open `V ∋ g(0')` the open `U ∩ V` contains `ζ` (`ζ ∈ D(x)` and
  `ζ ⤳ g(0')`), so `j_*(ℱ|_U)` has no nonzero section near `g(0')`.  Hence every map from
  `g^*(j_*(ℱ|_U))` to a skyscraper at the origin `0'` of `𝔸¹` vanishes, by `g^* ⊣ g_*`
  (`restrictedModule_hom_eq_zero`).
* `j'_*((g^*ℱ)|_{U'})`: the diagonal maps `U'` into `D(y)`, where `ℱ = 𝒪`, and the section `1`
  of `ℱ` over `D(y)` gives a section of `g^*ℱ` over `U'`, which the map
  `g^*ℱ ⟶ η'_*(𝒪_{𝔸¹,η'})` adjoint to "germ at `g(η')` followed by the stalk map of `g`" sends
  to `1 ≠ 0`, `η'` being the generic point of `𝔸¹`.  Since `η' ⤳ 0'`, this yields a nonzero map
  from `j'_*((g^*ℱ)|_{U'})` to the skyscraper at `0'` with value `𝒪_{𝔸¹,η'}`
  (`targetTest_ne_zero`).

So the degree-one terms are not isomorphic by any isomorphism (`isEmpty_iso_restrictedModule`),
the two complexes are not isomorphic (`isEmpty_iso_cplx`), and the repository's comparison maps
`restrictedModuleBaseChange` and `cplxBaseChange` are not isomorphisms
(`not_isIso_restrictedModuleBaseChange`, `not_isIso_cplxBaseChange_f_one`,
`not_isIso_cplxBaseChange`).  Consistently, `ℱ` is not quasi-coherent
(`not_isQuasicoherent_coeff`).

## Implementation notes

`ℱ` is built as the kernel of the germ map `𝒪_X ⟶ ζ_*(𝒪_{X,ζ})` (`germSky`, `germKernel`)
rather than as an extension by zero, because the sections of a kernel are computed sectionwise
(`SheafOfModules.evaluation` preserves limits): over an open containing `ζ` they vanish by
injectivity of the germ maps of an integral scheme (`subsingleton_germKernel`), and over an open
missing `ζ` every function is one (`exists_germKernelι_eq`).  The sections of `g^*ℱ` are never
computed: the section over `U'` is the image of `1` under the unit of `g^* ⊣ g_*`, and it is
evaluated through the adjoint of a map out of `ℱ` into a skyscraper, using
`Stacks.ModuleSkyscraper.pushSkyObjIso` for `g_*` of a skyscraper.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.ModuleSkyscraper
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.CechBaseChangeCounterexample

section General

variable {X : Scheme.{u}}

/-- The germ map `𝒪_X ⟶ x_*(𝒪_{X,x})` into the skyscraper at `x` with value the local ring. -/
def germSky (x : X) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      skyModules X x (ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x)) :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun r p => (X.presheaf.germ V.unop x p.down).hom r
          map_zero' := funext fun p => map_zero _
          map_add' := fun a b => funext fun p => map_add _ a b }
      naturality := fun {V W} i => by
        ext r
        funext p
        change (X.presheaf.germ W.unop x p.down).hom (X.presheaf.map i r) =
          (X.presheaf.germ V.unop x (i.unop.le p.down)).hom r
        exact X.presheaf.germ_res_apply i.unop x p.down r }
    (fun V r m => funext fun p => by
      let m' : X.presheaf.obj V := m
      let r' : X.presheaf.obj V := r
      change (X.presheaf.germ V.unop x p.down).hom (r' * m') =
        (X.presheaf.germ V.unop x p.down).hom r' * (X.presheaf.germ V.unop x p.down).hom m'
      exact map_mul _ r' m')⟩

/-- The germ map evaluates a section to its germ at `x`. -/
theorem germSky_app_apply (x : X) (V : X.Opens) (r : Γ(X, V)) (p : PLift (x ∈ V)) :
    Scheme.Modules.Hom.app (germSky x) V r p = (X.presheaf.germ V x p.down).hom r := rfl

/-- A point of an open `W` that lies in `V` lies in `W.ι ''ᵁ (W.ι ⁻¹ᵁ V)`. -/
theorem mem_image_preimage_ι {W V : X.Opens} {η : X} (hW : η ∈ W) (hV : η ∈ V) :
    η ∈ W.ι ''ᵁ (W.ι ⁻¹ᵁ V) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact ⟨hW, hV⟩

/-- **Restricting a skyscraper at a point `η` of an open `W` and specializing to `y`.**  For
`η ∈ W` and `η ⤳ y`, the morphism `j_{W,*}j_W^*(η_*A) ⟶ y_*(A)` that sends a section over `V`,
a function on `η ∈ W ∩ V` with values in `A`, to the function on `y ∈ V` given by the same value
(`y ∈ V` forces `η ∈ V`).  Here `A` is read over `𝒪_{X,y}` through the specialization map. -/
def pushRestrictSkyToSky (W : X.Opens) {η y : X} (hη : η ∈ W) (h : η ⤳ y)
    (A : ModuleCat.{u} (X.presheaf.stalk η)) :
    Stacks.AlgebraicGeometry.RelativeMayerVietoris.pushRestrict (skyModules X η A) W ⟶
      skyModules X y ((ModuleCat.restrictScalars (X.presheaf.stalkSpecializes h).hom).obj A) :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun g p => g ⟨mem_image_preimage_ι hη (h.mem_open V.unop.isOpen p.down)⟩
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      naturality := fun _ _ _ => rfl }
    (fun V r g => funext fun p => by
      let r' : Γ(X, V.unop) := r
      have key : (W.ι.app V.unop ≫ (W.ι.appIso (W.ι ⁻¹ᵁ V.unop)).inv ≫
            X.presheaf.germ (W.ι ''ᵁ (W.ι ⁻¹ᵁ V.unop)) η
              (mem_image_preimage_ι hη (h.mem_open V.unop.isOpen p.down))).hom r' =
          (X.presheaf.germ V.unop y p.down ≫ X.presheaf.stalkSpecializes h).hom r' := by
        rw [Scheme.Hom.app_appIso_inv_assoc]
        exact congrArg (fun φ => φ.hom r') ((X.presheaf.germ_res _ η _).trans
          (X.presheaf.germ_stalkSpecializes p.down h).symm)
      exact congrArg (· • g ⟨mem_image_preimage_ι hη (h.mem_open V.unop.isOpen p.down)⟩) key)⟩

/-- **Elements of a kernel of modules, sectionwise.**  If `G` preserves the kernel of `φ`, an
element of `G.obj M` killed by `G.map φ` comes from `G.obj (kernel φ)`. -/
theorem exists_map_kernelι_eq {C : Type*} [Category C] [HasZeroMorphisms C] {R : RingCat.{u}}
    (G : C ⥤ ModuleCat.{u} R) [G.PreservesZeroMorphisms] {M N : C} (φ : M ⟶ N) [HasKernel φ]
    [PreservesLimit (parallelPair φ 0) G] (m : G.obj M) (hm : G.map φ m = 0) :
    ∃ k : G.obj (kernel φ), G.map (kernel.ι φ) k = m := by
  let t : ModuleCat.of R R ⟶ G.obj M := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ m)
  have ht : t ≫ G.map φ = 0 := by
    ext1
    refine LinearMap.ext_ring ?_
    change G.map φ ((1 : R) • m) = 0
    rw [one_smul, hm]
  refine ⟨(kernel.lift (G.map φ) t ht ≫ (PreservesKernel.iso G φ).inv) 1, ?_⟩
  rw [← ConcreteCategory.comp_apply, Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]
  change (1 : R) • m = m
  exact one_smul R m

/-- **A kernel inclusion of modules is injective sectionwise.** -/
theorem injective_map_kernelι {C : Type*} [Category C] [HasZeroMorphisms C] {R : RingCat.{u}}
    (G : C ⥤ ModuleCat.{u} R) [G.PreservesZeroMorphisms] {M N : C} (φ : M ⟶ N) [HasKernel φ]
    [PreservesLimit (parallelPair φ 0) G] :
    Function.Injective (G.map (kernel.ι φ)) := by
  have : G.map (kernel.ι φ) = (PreservesKernel.iso G φ).hom ≫ kernel.ι (G.map φ) := by
    rw [← PreservesKernel.iso_inv_ι, Iso.hom_inv_id_assoc]
  rw [this]
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

/-- **The sheaf of functions with vanishing germ at `ζ`**: the kernel of `germSky ζ`.  Its
sections over an open `V` are the functions on `V` whose germ at `ζ` is zero when `ζ ∈ V`. -/
def germKernel (ζ : X) : X.Modules := kernel (germSky ζ)

/-- The inclusion of `germKernel ζ` into `𝒪_X`. -/
def germKernelι (ζ : X) : germKernel ζ ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (germSky ζ)

/-- On an open containing `ζ`, an integral scheme has no nonzero section with vanishing germ
at `ζ`. -/
theorem subsingleton_germKernel [IsIntegral X] (ζ : X) {V : X.Opens} (hV : ζ ∈ V) :
    Subsingleton Γ(germKernel ζ, V) := by
  refine ⟨fun a b => ?_⟩
  refine injective_map_kernelι (SheafOfModules.evaluation X.ringCatSheaf (op V)) (germSky ζ) ?_
  have hz : ∀ m : Γ(germKernel ζ, V),
      (SheafOfModules.evaluation X.ringCatSheaf (op V)).map (kernel.ι (germSky ζ)) m = 0 := by
    intro m
    apply germ_injective_of_isIntegral X ζ hV
    have h0 := congrArg (fun φ : germKernel ζ ⟶
        skyModules X ζ (ModuleCat.of (X.presheaf.stalk ζ) (X.presheaf.stalk ζ)) =>
        (show PLift (ζ ∈ V) → X.presheaf.stalk ζ from Scheme.Modules.Hom.app φ V m) ⟨hV⟩)
      (kernel.condition (germSky ζ))
    exact h0.trans (map_zero _).symm
  rw [hz a, hz b]

/-- On an open not containing `ζ`, every section of `𝒪_X` lies in `germKernel ζ`. -/
theorem exists_germKernelι_eq (ζ : X) {V : X.Opens} (hV : ζ ∉ V) (r : Γ(X, V)) :
    ∃ e : Γ(germKernel ζ, V), Scheme.Modules.Hom.app (germKernelι ζ) V e = r :=
  exists_map_kernelι_eq (SheafOfModules.evaluation X.ringCatSheaf (op V))
    (germSky ζ) (r : (SheafOfModules.unit X.ringCatSheaf).val.obj (op V))
    (funext fun p => (hV p.down).elim)

end General

section Example

open Stacks.Perfect.ExtendedAlternatingCech Stacks.Perfect.CechBaseChange
open Stacks.AlgebraicGeometry.RelativeMayerVietoris (pushRestrict)

variable (k : Type u) [Field k]

/-- The plane `𝔸²_k = Spec k[x, y]`, with `x = X 0` and `y = X 1`. -/
abbrev planeRing : CommRingCat.{u} := CommRingCat.of (MvPolynomial (Fin 2) k)

/-- The line `𝔸¹_k = Spec k[t]`. -/
abbrev lineRing : CommRingCat.{u} := CommRingCat.of (Polynomial k)

/-- The ring map of the diagonal `𝔸¹ ⟶ 𝔸²`: `x, y ↦ t`. -/
def diagHom : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C fun _ => Polynomial.X

/-- The ring map of the horizontal axis `𝔸¹ ⟶ 𝔸²`: `x ↦ t`, `y ↦ 0`. -/
def axisHom : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 0]

/-- The diagonal `g : 𝔸¹_k ⟶ 𝔸²_k`. -/
def diag : Spec (lineRing k) ⟶ Spec (planeRing k) := Spec.map (CommRingCat.ofHom (diagHom k))

/-- The single equation `f₁ = x` on `𝔸²_k`. -/
def eqns : Fin 1 → Γ(Spec (planeRing k), ⊤) :=
  fun _ => (Scheme.ΓSpecIso (planeRing k)).inv (MvPolynomial.X 0)

/-- The unique strictly increasing `1`-tuple of indices in `Fin 1`. -/
def idx : CechCochains.OrdIndex (I := Fin 1) 0 := ⟨fun i => i, fun _ _ h => h⟩

/-- The generic point `ζ` of the line `y = 0` in `𝔸²_k`. -/
def axisPoint : Spec (planeRing k) :=
  (⟨RingHom.ker (axisHom k), RingHom.ker_isPrime _⟩ : PrimeSpectrum (MvPolynomial (Fin 2) k))

/-- The origin `0'` of `𝔸¹_k`. -/
def lineOrigin : Spec (lineRing k) :=
  (⟨RingHom.ker (Polynomial.evalRingHom (0 : k)), RingHom.ker_isPrime _⟩ :
    PrimeSpectrum (Polynomial k))

/-- The generic point `η'` of `𝔸¹_k`. -/
def lineGeneric : Spec (lineRing k) :=
  (⟨⊥, inferInstance⟩ : PrimeSpectrum (Polynomial k))

/-- **The coefficient module of the counterexample**: the sheaf `ℱ` of functions on `𝔸²_k`
whose germ at the generic point of the line `y = 0` vanishes.  It is the extension by zero of
`𝒪` from `D(y)`, and it is not quasi-coherent. -/
def coeff : (Spec (planeRing k)).Modules := germKernel (axisPoint k)

/-- Membership in a principal open of `𝔸²_k`, at the level of prime ideals. -/
theorem mem_basicOpen_plane (p : Spec (planeRing k)) (r : MvPolynomial (Fin 2) k) :
    p ∈ (Spec (planeRing k)).basicOpen ((Scheme.ΓSpecIso (planeRing k)).inv r) ↔
      r ∉ (show PrimeSpectrum (MvPolynomial (Fin 2) k) from p).asIdeal := by
  rw [basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- The open `U` of the single equation `x` is `D(x)`. -/
theorem equationsOpen_eqns :
    equationsOpen (eqns k) 0 idx =
      (Spec (planeRing k)).basicOpen ((Scheme.ΓSpecIso (planeRing k)).inv (MvPolynomial.X 0)) := by
  unfold equationsOpen eqns
  exact iInf_const

/-- The diagonal sends both coordinates to `t`. -/
theorem diagHom_X (i : Fin 2) : diagHom k (MvPolynomial.X i) = Polynomial.X :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- A point of `𝔸¹_k` lies over `D(x)`, resp. `D(y)`, exactly when `t` does not vanish there. -/
theorem mem_diag_preimage_basicOpen (q : Spec (lineRing k)) (i : Fin 2) :
    q ∈ diag k ⁻¹ᵁ (Spec (planeRing k)).basicOpen
        ((Scheme.ΓSpecIso (planeRing k)).inv (MvPolynomial.X i)) ↔
      (Polynomial.X : Polynomial k) ∉ (show PrimeSpectrum (Polynomial k) from q).asIdeal := by
  change (diag k).base q ∈ (Spec (planeRing k)).basicOpen
    ((Scheme.ΓSpecIso (planeRing k)).inv (MvPolynomial.X i)) ↔ _
  rw [mem_basicOpen_plane]
  change MvPolynomial.X i ∉ Ideal.comap (diagHom k) _ ↔ _
  rw [Ideal.mem_comap, diagHom_X]

/-- `ζ` specializes to the image `g(0')` of the origin, which is the origin of `𝔸²_k`. -/
theorem axisPoint_specializes : axisPoint k ⤳ (diag k).base (lineOrigin k) := by
  refine (PrimeSpectrum.le_iff_specializes (R := MvPolynomial (Fin 2) k) _ _).mp ?_
  intro r hr
  change r ∈ Ideal.comap (diagHom k) (RingHom.ker (Polynomial.evalRingHom (0 : k)))
  have hr : axisHom k r = 0 := hr
  have heq : (Polynomial.evalRingHom (0 : k)).comp (diagHom k) =
      (Polynomial.evalRingHom (0 : k)).comp (axisHom k) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [diagHom, axisHom]
    · fin_cases i <;> simp [diagHom, axisHom]
  rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, heq, RingHom.comp_apply, hr,
    map_zero]

/-- `ζ` lies in `U = D(x)`. -/
theorem axisPoint_mem_equationsOpen : axisPoint k ∈ equationsOpen (eqns k) 0 idx := by
  rw [equationsOpen_eqns, mem_basicOpen_plane]
  change MvPolynomial.X 0 ∉ RingHom.ker (axisHom k)
  rw [RingHom.mem_ker]
  simp [axisHom]

/-- `ζ` does not lie in `D(y)`. -/
theorem axisPoint_not_mem_basicOpen_y :
    axisPoint k ∉ (Spec (planeRing k)).basicOpen
      ((Scheme.ΓSpecIso (planeRing k)).inv (MvPolynomial.X 1)) := by
  rw [mem_basicOpen_plane, not_not]
  change axisHom k (MvPolynomial.X 1) = 0
  simp [axisHom]

/-- The open `U' = D(t)` of the pulled-back equation. -/
abbrev lineOpen : (Spec (lineRing k)).Opens :=
  equationsOpen (fun j => (diag k).appTop (eqns k j)) 0 idx

/-- `U'` is the inverse image of `U`. -/
theorem lineOpen_eq : lineOpen k = diag k ⁻¹ᵁ equationsOpen (eqns k) 0 idx :=
  (equationsOpen_pullback (diag k) (eqns k) 0 idx).symm

/-- The generic point `η'` lies in `U' = D(t)`. -/
theorem lineGeneric_mem_lineOpen : lineGeneric k ∈ lineOpen k := by
  rw [lineOpen_eq, equationsOpen_eqns, mem_diag_preimage_basicOpen]
  exact Polynomial.X_ne_zero

/-- The generic point `η'` specializes to the origin `0'`. -/
theorem lineGeneric_specializes : lineGeneric k ⤳ lineOrigin k :=
  (PrimeSpectrum.le_iff_specializes (R := Polynomial k) _ _).mp bot_le

/-- The diagonal maps `U' = D(t)` into `D(y)`. -/
theorem lineOpen_le : lineOpen k ≤ diag k ⁻¹ᵁ (Spec (planeRing k)).basicOpen
    ((Scheme.ΓSpecIso (planeRing k)).inv (MvPolynomial.X 1)) := by
  intro q hq
  have hq' : q ∈ lineOpen k := hq
  rw [lineOpen_eq, equationsOpen_eqns, mem_diag_preimage_basicOpen] at hq'
  exact (mem_diag_preimage_basicOpen k q 1).mpr hq'

/-- **On the source side every map into a pushed-forward skyscraper at `g(0')` vanishes.**
The Čech term `j_*(ℱ|_U)` has no nonzero section over an open `V ∋ g(0')`, because such a `V`
contains `ζ`, and so does `U`; and the pushed-forward skyscraper has no nonzero section over an
open `V ∌ g(0')`. -/
theorem restrictedModule_hom_eq_zero (A : ModuleCat.{u} ((Spec (lineRing k)).presheaf.stalk
      (lineOrigin k)))
    (β : restrictedModule (eqns k) (coeff k) 0 idx ⟶
      (Scheme.Modules.pushforward (diag k)).obj (skyModules _ (lineOrigin k) A)) :
    β = 0 := by
  have h : toRPhom (eqns k) (coeff k) 0 idx ≫ β = 0 := by
    ext V x
    by_cases hV : (diag k).base (lineOrigin k) ∈ V
    · have : Subsingleton Γ(coeff k, (equationsOpen (eqns k) 0 idx).ι ''ᵁ
          ((equationsOpen (eqns k) 0 idx).ι ⁻¹ᵁ V)) :=
        subsingleton_germKernel (axisPoint k) (mem_image_preimage_ι
          (axisPoint_mem_equationsOpen k) ((axisPoint_specializes k).mem_open V.isOpen hV))
      have hx : x = 0 := Subsingleton.elim (α := Γ(coeff k, (equationsOpen (eqns k) 0 idx).ι ''ᵁ
          ((equationsOpen (eqns k) 0 idx).ι ⁻¹ᵁ V))) x 0
      rw [hx, map_zero, map_zero]
    · exact funext fun p => (hV p.down).elim
  rw [← Category.id_comp β, ← toRPinv_toRPhom (eqns k) (coeff k) 0 idx, Category.assoc, h,
    comp_zero]

/-- The local ring `𝒪_{𝔸¹,η'}` at the generic point of the line, as a module over itself. -/
abbrev genericStalk : ModuleCat.{u} ((Spec (lineRing k)).presheaf.stalk (lineGeneric k)) :=
  ModuleCat.of _ ((Spec (lineRing k)).presheaf.stalk (lineGeneric k))

/-- The stalk map `𝒪_{𝔸²,g(η')} ⟶ 𝒪_{𝔸¹,η'}` of the diagonal, as a linear map. -/
def diagStalkLinear :
    ModuleCat.of ((Spec (planeRing k)).presheaf.stalk ((diag k).base (lineGeneric k)))
        ((Spec (planeRing k)).presheaf.stalk ((diag k).base (lineGeneric k))) ⟶
      (ModuleCat.restrictScalars ((diag k).stalkMap (lineGeneric k)).hom).obj
        (genericStalk k) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars ((diag k).stalkMap (lineGeneric k)).hom).obj
      (genericStalk k))
    { toFun := ((diag k).stalkMap (lineGeneric k)).hom
      map_add' := map_add _
      map_smul' := fun r m => map_mul ((diag k).stalkMap (lineGeneric k)).hom r m }

/-- The test map `ℱ ⟶ g(η')_*(𝒪_{𝔸¹,η'})`: include `ℱ` into `𝒪`, take the germ at `g(η')` and
apply the stalk map of the diagonal. -/
def testMapFlat : coeff k ⟶ skyModules (Spec (planeRing k)) ((diag k).base (lineGeneric k))
    ((ModuleCat.restrictScalars ((diag k).stalkMap (lineGeneric k)).hom).obj (genericStalk k)) :=
  germKernelι (axisPoint k) ≫ germSky ((diag k).base (lineGeneric k)) ≫
    (skyModulesFunctor (Spec (planeRing k)) ((diag k).base (lineGeneric k))).map
      (diagStalkLinear k)

/-- Its adjoint `g^*ℱ ⟶ η'_*(𝒪_{𝔸¹,η'})`. -/
def testMap : (Scheme.Modules.pullback (diag k)).obj (coeff k) ⟶
    skyModules (Spec (lineRing k)) (lineGeneric k) (genericStalk k) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (diag k)).homEquiv _ _).symm
    (testMapFlat k ≫ (pushSkyObjIso (diag k) (lineGeneric k) (genericStalk k)).inv)

/-- The map `j'_*((g^*ℱ)|_{U'}) ⟶ 0'_*(𝒪_{𝔸¹,η'})` on the target side. -/
def targetTest : pushRestrict ((Scheme.Modules.pullback (diag k)).obj (coeff k)) (lineOpen k) ⟶
    skyModules (Spec (lineRing k)) (lineOrigin k)
      ((ModuleCat.restrictScalars ((Spec (lineRing k)).presheaf.stalkSpecializes
        (lineGeneric_specializes k)).hom).obj (genericStalk k)) :=
  (Scheme.Modules.pushforward (lineOpen k).ι).map
      ((Scheme.Modules.restrictFunctor (lineOpen k).ι).map (testMap k)) ≫
    pushRestrictSkyToSky (lineOpen k) (lineGeneric_mem_lineOpen k) (lineGeneric_specializes k)
      (genericStalk k)

/-- **On the target side the test map is nonzero.** -/
theorem targetTest_ne_zero : targetTest k ≠ 0 := by
  intro h0
  set W := (Spec (planeRing k)).basicOpen
    ((Scheme.ΓSpecIso (planeRing k)).inv (MvPolynomial.X 1)) with hW
  obtain ⟨e, he⟩ := exists_germKernelι_eq (axisPoint k) (axisPoint_not_mem_basicOpen_y k)
    (1 : Γ(Spec (planeRing k), W))
  set H := (Scheme.Modules.pullback (diag k)).obj (coeff k)
  have hle : (lineOpen k).ι ''ᵁ ((lineOpen k).ι ⁻¹ᵁ ⊤) ≤ diag k ⁻¹ᵁ W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_le_left.trans (lineOpen_le k)
  let s0 : Γ(H, diag k ⁻¹ᵁ W) :=
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction (diag k)).unit.app
      (coeff k)) W e
  let s1 : Γ(H, (lineOpen k).ι ''ᵁ ((lineOpen k).ι ⁻¹ᵁ ⊤)) := H.presheaf.map (homOfLE hle).op s0
  have hmem0 : lineOrigin k ∈ (⊤ : (Spec (lineRing k)).Opens) := trivial
  have hval : (show PLift (lineOrigin k ∈ (⊤ : (Spec (lineRing k)).Opens)) →
      (Spec (lineRing k)).presheaf.stalk (lineGeneric k) from
        Scheme.Modules.Hom.app (targetTest k) ⊤ s1) ⟨hmem0⟩ = 1 := by
    have hmem1 : lineGeneric k ∈ (lineOpen k).ι ''ᵁ ((lineOpen k).ι ⁻¹ᵁ ⊤) :=
      mem_image_preimage_ι (lineGeneric_mem_lineOpen k) trivial
    have hmem2 : lineGeneric k ∈ diag k ⁻¹ᵁ W := hle hmem1
    have step1 : (show PLift (lineOrigin k ∈ (⊤ : (Spec (lineRing k)).Opens)) →
        (Spec (lineRing k)).presheaf.stalk (lineGeneric k) from
          Scheme.Modules.Hom.app (targetTest k) ⊤ s1) ⟨hmem0⟩ =
        (show PLift (lineGeneric k ∈ (lineOpen k).ι ''ᵁ ((lineOpen k).ι ⁻¹ᵁ ⊤)) →
          (Spec (lineRing k)).presheaf.stalk (lineGeneric k) from
          Scheme.Modules.Hom.app (testMap k) _ s1) ⟨hmem1⟩ := rfl
    have hnat : Scheme.Modules.Hom.app (testMap k) _ s1 =
        (skyModules (Spec (lineRing k)) (lineGeneric k) (genericStalk k)).presheaf.map
          (homOfLE hle).op (Scheme.Modules.Hom.app (testMap k) _ s0) :=
      ConcreteCategory.congr_hom ((testMap k).mapPresheaf.naturality (homOfLE hle).op) s0
    have key : (Scheme.Modules.pullbackPushforwardAdjunction (diag k)).unit.app (coeff k) ≫
        (Scheme.Modules.pushforward (diag k)).map (testMap k) =
          testMapFlat k ≫ (pushSkyObjIso (diag k) (lineGeneric k) (genericStalk k)).inv :=
      ((Scheme.Modules.pullbackPushforwardAdjunction (diag k)).homEquiv_unit _ _
        (testMap k)).symm.trans (Equiv.apply_symm_apply _ _)
    have step3 : Scheme.Modules.Hom.app (testMap k) (diag k ⁻¹ᵁ W) s0 =
        Scheme.Modules.Hom.app (testMapFlat k ≫
          (pushSkyObjIso (diag k) (lineGeneric k) (genericStalk k)).inv) W e := by
      rw [← key]
      rfl
    rw [step1, hnat, step3]
    change ((diag k).stalkMap (lineGeneric k)).hom (((Spec (planeRing k)).presheaf.germ W _
      hmem2).hom (Scheme.Modules.Hom.app (germKernelι (axisPoint k)) W e)) = 1
    rw [he]
    change ((diag k).stalkMap (lineGeneric k)).hom
      (((Spec (planeRing k)).presheaf.germ W _ hmem2).hom 1) = 1
    rw [map_one, map_one]
  rw [h0] at hval
  have h01 : (0 : (Spec (lineRing k)).presheaf.stalk (lineGeneric k)) = 1 := hval
  exact zero_ne_one h01

/-- **No isomorphism at all between the degree-one terms.**  There is no isomorphism of
`𝒪_{𝔸¹}`-modules `g^*(j_*(ℱ|_U)) ≅ j'_*((g^*ℱ)|_{U'})`: every map from the source to the
skyscraper `0'_*(𝒪_{𝔸¹,η'})` vanishes (`restrictedModule_hom_eq_zero`, through the adjunction
`g^* ⊣ g_*`), while `targetTest` is a nonzero map from the target to it. -/
theorem isEmpty_iso_restrictedModule :
    IsEmpty ((Scheme.Modules.pullback (diag k)).obj (restrictedModule (eqns k) (coeff k) 0 idx) ≅
      restrictedModule (fun j => (diag k).appTop (eqns k j))
        ((Scheme.Modules.pullback (diag k)).obj (coeff k)) 0 idx) := by
  refine ⟨fun e => ?_⟩
  let ψN := toRPinv (fun j => (diag k).appTop (eqns k j))
    ((Scheme.Modules.pullback (diag k)).obj (coeff k)) 0 idx ≫ targetTest k
  have hzero : e.hom ≫ ψN = 0 := by
    let adj := Scheme.Modules.pullbackPushforwardAdjunction (diag k)
    have h1 : adj.homEquiv _ _ (e.hom ≫ ψN) = 0 := restrictedModule_hom_eq_zero k _ _
    rw [← (adj.homEquiv _ _).symm_apply_apply (e.hom ≫ ψN), h1, Adjunction.homEquiv_counit,
      Functor.map_zero, zero_comp]
  have hψN : ψN = 0 := by
    rw [← Category.id_comp ψN, ← e.inv_hom_id, Category.assoc, hzero, comp_zero]
  apply targetTest_ne_zero k
  rw [← Category.id_comp (targetTest k), ← toRPhom_toRPinv, Category.assoc]
  exact (congrArg _ hψN).trans comp_zero

/-- The termwise comparison `restrictedModuleBaseChange` of [Stacks, Tag 0G7U] is not an
isomorphism for these data. -/
theorem not_isIso_restrictedModuleBaseChange :
    ¬ IsIso (restrictedModuleBaseChange (diag k) (eqns k) (coeff k) 0 idx) :=
  fun _ => (isEmpty_iso_restrictedModule k).false
    (asIso (restrictedModuleBaseChange (diag k) (eqns k) (coeff k) 0 idx))

/-- The unique strictly increasing `1`-tuple in `Fin 1`. -/
@[instance_reducible]
def uniqueIdx : Unique (CechCochains.OrdIndex (I := Fin 1) 0) where
  default := idx
  uniq _ := Subtype.ext (funext fun _ => Subsingleton.elim _ _)

attribute [local instance] uniqueIdx

/-- The degree-one terms of the two complexes are not isomorphic. -/
private theorem false_of_iso_cplx_X_one
    (e : (Scheme.Modules.pullback (diag k)).obj ((cplx (eqns k) (coeff k)).X 1) ≅
      (cplx (fun j => (diag k).appTop (eqns k j))
        ((Scheme.Modules.pullback (diag k)).obj (coeff k))).X 1) : False :=
  (isEmpty_iso_restrictedModule k).false
    ((Scheme.Modules.pullback (diag k)).mapIso (productUniqueIso _).symm ≪≫ e ≪≫
      productUniqueIso _)

/-- **No isomorphism at all between the extended alternating Čech complexes**
`g^*(ℱ^•)` and `(g^*ℱ)^•` of the counterexample: their degree-one terms are a single
`g^*(j_*(ℱ|_U))`, resp. `j'_*((g^*ℱ)|_{U'})`, and these are not isomorphic
(`isEmpty_iso_restrictedModule`).  This refutes the note `(ℱ')^• = g^*ℱ^•` of
[Stacks, Tag 0G7U] for non-quasi-coherent `ℱ` in its strongest reading, with no comparison map
fixed in advance. -/
@[stacks 0G7U "refutes the note `(F')^• = g^*F^•` for a non-quasi-coherent `F`: for the diagonal \
`A^1 → A^2`, `f_1 = x` and `F` the extension by zero of `O` from `D(y)`, the two complexes are \
not isomorphic at all; the quasi-coherent form is `isIso_cplxBaseChange`"]
theorem isEmpty_iso_cplx :
    IsEmpty (((Scheme.Modules.pullback (diag k)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (cplx (eqns k) (coeff k)) ≅
      cplx (fun j => (diag k).appTop (eqns k j)) ((Scheme.Modules.pullback (diag k)).obj
        (coeff k))) := by
  exact ⟨fun e => false_of_iso_cplx_X_one k ((HomologicalComplex.eval _ _ 1).mapIso e)⟩

/-- **The base-change comparison of complexes of [Stacks, Tag 0G7U] is not an isomorphism for
the non-quasi-coherent module `ℱ = coeff k`**, already in degree `1`.  Here `k` is any field,
`g : 𝔸¹_k ⟶ 𝔸²_k` is the diagonal, the single equation is `x`, and `ℱ` is the sheaf of functions
with vanishing germ at the generic point of the line `y = 0` (the extension by zero of `𝒪` from
`D(y)`).  So the note `(ℱ')^• = g^*ℱ^•` of the remark, read through the comparison map
`cplxBaseChange`, is false for an arbitrary `𝒪_X`-module; for quasi-coherent `ℱ` it holds
(`Stacks.Perfect.CechBaseChange.isIso_cplxBaseChange`). -/
@[stacks 0G7U "refutes the note `(F')^• = g^*F^•` for a non-quasi-coherent `F`: the comparison \
`cplxBaseChange` is not an isomorphism in degree 1 for the diagonal `A^1 → A^2`, `f_1 = x` and \
`F` the extension by zero of `O` from `D(y)`; the quasi-coherent form is `isIso_cplxBaseChange`"]
theorem not_isIso_cplxBaseChange_f_one :
    ¬ IsIso ((cplxBaseChange (diag k) (eqns k) (coeff k)).f 1) := by
  intro h
  exact false_of_iso_cplx_X_one k (asIso ((cplxBaseChange (diag k) (eqns k) (coeff k)).f 1))

/-- The comparison of complexes `cplxBaseChange` is not an isomorphism for these data. -/
theorem not_isIso_cplxBaseChange : ¬ IsIso (cplxBaseChange (diag k) (eqns k) (coeff k)) :=
  fun _ => not_isIso_cplxBaseChange_f_one k inferInstance

/-- **The coefficient module of the counterexample is not quasi-coherent**, as it must not be:
for a quasi-coherent module the comparison is an isomorphism (`isIso_cplxBaseChange`). -/
theorem not_isQuasicoherent_coeff : ¬ (coeff k).IsQuasicoherent :=
  fun _ => not_isIso_cplxBaseChange k (isIso_cplxBaseChange (diag k) (eqns k) (coeff k))

end Example

end Stacks.Perfect.CechBaseChangeCounterexample

end
