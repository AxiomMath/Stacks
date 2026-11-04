module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Linear.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison

/-!
# The maps on `Ext` induced by a map of free resolutions depend only on the module map

Let `R` be a ring, let `M₁`, `M₂`, `N` be `R`-modules, let `F_•` be a free resolution of `M₁`,
let `G_•` be a free resolution of `M₂` and let `φ : M₁ → M₂` be a module map. By Stacks 00LS there
is a map of complexes `α : F_• → G_•` inducing `φ` on `M₁ = Coker(d_{F, 1}) → M₂ = Coker(d_{G, 1})`,
and any two such maps are homotopic. Applying `Hom_R(-, N)` turns `α` into a map of cochain
complexes `Hom_R(G_•, N) → Hom_R(F_•, N)`, hence into maps

`H^i(α) : H^i(Hom_R(G_•, N)) → H^i(Hom_R(F_•, N))`

on cohomology, that is, into maps `Ext^i_R(M₂, N) → Ext^i_R(M₁, N)`. These maps do not depend on
the choice of `α`: any other map of complexes inducing `φ` gives the same maps. If `φ` is an
isomorphism they are isomorphisms, and a map `F_• → F_•` inducing the identity of `M₁` induces the
identity on `H^i(Hom_R(F_•, N))`. Together these three statements are what makes `Ext^i_R(M, N)`,
defined as `H^i(Hom_R(F_•, N))` for a free resolution `F_•` of `M`, independent of the resolution
up to a canonical isomorphism.

## Main results

* `ModuleCat.homologyMap_linearYoneda_eq_and_isIso_and_eq_id`: the maps `H^i(α)` above are
  independent of the choice of `α`, are isomorphisms when `φ` is one, and are the identity when
  `α` is a lift of the identity to a single resolution.

## Implementation notes

A free resolution is this project's `CategoryTheory.ObjectProperty.LeftResolution` (Stacks 00LQ)
for the class of free modules: a chain complex `F.complex` of free `R`-modules together with an
augmentation `F.π : F.complex ⟶ M[0]` which is a quasi-isomorphism, i.e. with
`… → F₁ → F₀ → M → 0` exact. The source's identification `M₁ = Coker(d_{F, 1})` is carried by that
augmentation, and "`α` induces `φ`" is the commuting square
`α ≫ G.π = F.π ≫ (ChainComplex.single₀ _).map φ`, the shape of
`CategoryTheory.ProjectiveResolution.lift_commutes`.

The complex `Hom_R(F_•, N)` is the image of `F_•` under `Hom_R(-, N)`, the functor
`(CategoryTheory.linearYoneda R (ModuleCat R)).obj N` on `(ModuleCat R)ᵒᵖ`, applied degreewise:
`HomologicalComplex.opFunctor` turns the chain complex `F_•` into a cochain complex in the opposite
category and `Functor.mapHomologicalComplex` applies `Hom_R(-, N)` to it. Its shape
`(ComplexShape.down ℕ).symm` is `ComplexShape.up ℕ`, so `HomologicalComplex.homology i` of it is
the source's `H^i(Hom_R(F_•, N))`.

The source displays `H^i(α)` as a map from the `F_•` side to the `G_•` side. No such map is induced
by `α`: `Hom_R(-, N)` is contravariant, so `α : F_• → G_•` induces `Hom_R(G_•, N) → Hom_R(F_•, N)`
and hence `Ext^i_R(M₂, N) → Ext^i_R(M₁, N)`, which is also the variance the source's own proof uses
when it composes a lift of `φ` with a lift of an inverse of `φ`. The arrows in the source's display
therefore point the wrong way, as does the subscript in its final clause's `H_i(α)`, where `H^i(α)`
is meant.

Nothing in the argument is about free modules, about modules, or about `Hom_R(-, N)`: it needs the
terms of the resolutions to be projective, and it needs the functor applied to them degreewise to
be additive. So all three assertions are proved here for a `CategoryTheory.ProjectiveResolution` in
an abelian category and an arbitrary additive `Φ : Cᵒᵖ ⥤ D` into a category with homology, and
00LT is the case `C = D = ModuleCat R`, `Φ = Hom_R(-, N)`. The single homotopy-theoretic step,
valid over a merely preadditive `C`, is that homotopic maps of chain complexes induce the same map
on the homology of their images under `Φ`, a homotopy surviving both the passage to the opposite
category and the degreewise application of `Φ` (Lemma 00LR).

The source's ring is arbitrary, whereas `R` is commutative here: `Hom_R(-, N)` is a functor to
`R`-modules, and `ModuleCat R` an `R`-linear category, only for commutative `R`. Over a general
ring the three assertions hold with `Hom_R(-, N)` valued in abelian groups, which is again a case
of the additive `Φ` treated below.

The third assertion is stated for one resolution and an endomorphism of it inducing the identity,
which is the meaning of the source's "`M₁ = M₂`, `F_• = G_•` and `φ` the identity" without an
equality of resolutions.

The first assertion has content: for `R = ℤ`, `M₁ = M₂ = ℤ/2ℤ`, both resolutions
`0 → ℤ ⟶[·2] ℤ → ℤ/2ℤ → 0`, `φ` the identity and `N = ℤ/2ℤ`, the lifts of `φ` are the maps given
by multiplication by an odd integer in both degrees, so there is more than one lift, while
`H^1(Hom_ℤ(F_•, N)) = Ext^1_ℤ(ℤ/2ℤ, ℤ/2ℤ) = ℤ/2ℤ` is nonzero.

## References

* [Stacks Project, Tag 00LT](https://stacks.math.columbia.edu/tag/00LT), Lemma 10.71.5, together
  with the Lemmas 00LQ, 00LR and 00LS it uses.
-/

@[expose] public section

universe v u

open CategoryTheory HomologicalComplex

section Homotopy

variable {C : Type*} [Category* C] [Preadditive C] {D : Type*} [Category* D] [Preadditive D]
  (Φ : Cᵒᵖ ⥤ D) [Φ.Additive]

/-- The contravariant functor taking a chain complex `K_•` in `C` to `Φ(K_•)`, the cochain complex
obtained by passing to the opposite complex and applying `Φ : Cᵒᵖ ⥤ D` degreewise. For
`Φ = Hom_R(-, N)` it is `K_• ↦ Hom_R(K_•, N)`. -/
private abbrev mapOp : (ChainComplex C ℕ)ᵒᵖ ⥤ HomologicalComplex D (ComplexShape.down ℕ).symm :=
  opFunctor C _ ⋙ Φ.mapHomologicalComplex _

/-- **Lemma 00LR, transported through `Φ`.** Homotopic maps of chain complexes `f, g : K_• ⟶ L_•`
induce the same map `H^i(Φ(L_•)) ⟶ H^i(Φ(K_•))`. -/
private lemma homologyMap_mapOp_eq_of_homotopy [CategoryWithHomology D] {K L : ChainComplex C ℕ}
    {f g : K ⟶ L} (h : Homotopy f g) (i : ℕ) :
    homologyMap ((mapOp Φ).map f.op) i = homologyMap ((mapOp Φ).map g.op) i :=
  (Φ.mapHomotopy h.op).homologyMap_eq i

end Homotopy

section Projective

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Preadditive D]
  [CategoryWithHomology D] (Φ : Cᵒᵖ ⥤ D) [Φ.Additive]

/-- **Lemmas 00LS and 00LR.** Two maps of complexes `α, β : P_• ⟶ Q_•` between projective
resolutions which both lift `φ : X ⟶ Y` induce the same map `H^i(Φ(Q_•)) ⟶ H^i(Φ(P_•))`. -/
private lemma homologyMap_mapOp_eq_of_comp_π_eq {X Y : C} (P : ProjectiveResolution X)
    (Q : ProjectiveResolution Y) (φ : X ⟶ Y) (α β : P.complex ⟶ Q.complex)
    (hα : α ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map φ)
    (hβ : β ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map φ) (i : ℕ) :
    homologyMap ((mapOp Φ).map β.op) i = homologyMap ((mapOp Φ).map α.op) i :=
  homologyMap_mapOp_eq_of_homotopy Φ (ProjectiveResolution.liftHomotopy φ β α hβ hα) i

/-- An endomorphism `γ` of a projective resolution `P_•` of `X` which lifts the identity of `X`
induces the identity of `H^i(Φ(P_•))`. -/
private lemma homologyMap_mapOp_eq_id_of_comp_π_eq {X : C} (P : ProjectiveResolution X)
    (γ : P.complex ⟶ P.complex) (hγ : γ ≫ P.π = P.π) (i : ℕ) :
    homologyMap ((mapOp Φ).map γ.op) i = 𝟙 _ := by
  rw [homologyMap_mapOp_eq_of_comp_π_eq Φ P P (𝟙 X) (𝟙 P.complex) γ (by simp) (by simpa using hγ) i]
  simp

/-- If `α : P_• ⟶ Q_•` lifts `φ : X ⟶ Y`, if `β : Q_• ⟶ P_•` lifts `ψ : Y ⟶ X` and if
`φ ≫ ψ = 𝟙 X`, then the two induced maps on homology compose to the identity of `H^i(Φ(P_•))`. -/
private lemma homologyMap_mapOp_comp_eq_id {X Y : C} (P : ProjectiveResolution X)
    (Q : ProjectiveResolution Y) {φ : X ⟶ Y} {ψ : Y ⟶ X} (hφψ : φ ≫ ψ = 𝟙 X)
    {α : P.complex ⟶ Q.complex} {β : Q.complex ⟶ P.complex}
    (hα : α ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map φ)
    (hβ : β ≫ P.π = Q.π ≫ (ChainComplex.single₀ C).map ψ) (i : ℕ) :
    homologyMap ((mapOp Φ).map β.op) i ≫ homologyMap ((mapOp Φ).map α.op) i = 𝟙 _ := by
  have h : (α ≫ β) ≫ P.π = P.π := by
    rw [Category.assoc, hβ, ← Category.assoc, hα, Category.assoc, ← Functor.map_comp, hφψ]
    simp
  rw [← homologyMap_comp, ← Functor.map_comp, ← op_comp,
    homologyMap_mapOp_eq_id_of_comp_π_eq Φ P (α ≫ β) h i]

/-- If `φ : X ⟶ Y` is an isomorphism, a map of complexes `α : P_• ⟶ Q_•` between projective
resolutions which lifts it induces an isomorphism `H^i(Φ(Q_•)) ⟶ H^i(Φ(P_•))`. -/
private lemma isIso_homologyMap_mapOp_of_comp_π_eq {X Y : C} (P : ProjectiveResolution X)
    (Q : ProjectiveResolution Y) (φ : X ⟶ Y) [IsIso φ] (α : P.complex ⟶ Q.complex)
    (hα : α ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map φ) (i : ℕ) :
    IsIso (homologyMap ((mapOp Φ).map α.op) i) := by
  have hβ := ProjectiveResolution.lift_commutes (inv φ) Q P
  exact ⟨⟨_, homologyMap_mapOp_comp_eq_id Φ Q P (by simp) hβ hα i,
    homologyMap_mapOp_comp_eq_id Φ P Q (by simp) hα hβ i⟩⟩

end Projective

namespace CategoryTheory.ObjectProperty.LeftResolution

/-- A resolution of an `R`-module by free modules (Stacks 00LQ), read as a projective resolution:
a free module is projective. -/
private def toProjectiveResolutionOfFree {R : Type u} [Ring R] {M : ModuleCat.{v} R}
    (F : LeftResolution (fun P : ModuleCat.{v} R => Module.Free R P) M) :
    ProjectiveResolution M where
  complex := F.complex
  projective n := by
    have : Module.Free R (F.complex.X n) := F.property n
    infer_instance
  π := F.π

end CategoryTheory.ObjectProperty.LeftResolution

namespace ModuleCat

/-- **Stacks 00LT.** Let `R` be a ring, let `M₁`, `M₂`, `N` be `R`-modules, let `F` be a free
resolution of `M₁`, let `G` be a free resolution of `M₂`, let `φ : M₁ → M₂` be a module map and
let `α : F_• → G_•` be a map of complexes inducing `φ`. Then, for every `i`, the map
`H^i(α) : H^i(Hom_R(G_•, N)) → H^i(Hom_R(F_•, N))` is independent of the choice of `α`; it is an
isomorphism if `φ` is one; and a map `F_• → F_•` inducing the identity of `M₁` induces the
identity on `H^i(Hom_R(F_•, N))`. -/
@[stacks 00LT "A free resolution is an `ObjectProperty.LeftResolution` for the class of free
modules (00LQ) and `Hom_R(F_•, N)` is the image of `F_•` under
`(linearYoneda R (ModuleCat R)).obj N`, so `H^i(α)` is a `homologyMap`. The source's display has
the two cohomology groups interchanged, since `Hom_R(-, N)` is contravariant; see the module
docstring."]
public theorem homologyMap_linearYoneda_eq_and_isIso_and_eq_id {R : Type u} [CommRing R]
    {M₁ M₂ : ModuleCat.{v} R} (N : ModuleCat.{v} R)
    (F : ObjectProperty.LeftResolution (fun P : ModuleCat.{v} R => Module.Free R P) M₁)
    (G : ObjectProperty.LeftResolution (fun P : ModuleCat.{v} R => Module.Free R P) M₂)
    (φ : M₁ ⟶ M₂) (α : F.complex ⟶ G.complex)
    (hα : α ≫ G.π = F.π ≫ (ChainComplex.single₀ (ModuleCat.{v} R)).map φ) (i : ℕ) :
    (∀ β : F.complex ⟶ G.complex,
        β ≫ G.π = F.π ≫ (ChainComplex.single₀ (ModuleCat.{v} R)).map φ →
        homologyMap ((opFunctor _ _ ⋙
            ((linearYoneda R (ModuleCat.{v} R)).obj N).mapHomologicalComplex _).map β.op) i =
          homologyMap ((opFunctor _ _ ⋙
            ((linearYoneda R (ModuleCat.{v} R)).obj N).mapHomologicalComplex _).map α.op) i) ∧
      (IsIso φ → IsIso (homologyMap ((opFunctor _ _ ⋙
          ((linearYoneda R (ModuleCat.{v} R)).obj N).mapHomologicalComplex _).map α.op) i)) ∧
      (∀ γ : F.complex ⟶ F.complex, γ ≫ F.π = F.π →
        homologyMap ((opFunctor _ _ ⋙
          ((linearYoneda R (ModuleCat.{v} R)).obj N).mapHomologicalComplex _).map γ.op) i
            = 𝟙 _) :=
  ⟨fun β hβ => homologyMap_mapOp_eq_of_comp_π_eq _ F.toProjectiveResolutionOfFree
      G.toProjectiveResolutionOfFree φ α β hα hβ i,
    fun _ => isIso_homologyMap_mapOp_of_comp_π_eq _ F.toProjectiveResolutionOfFree
      G.toProjectiveResolutionOfFree φ α hα i,
    fun γ hγ => homologyMap_mapOp_eq_id_of_comp_π_eq _ F.toProjectiveResolutionOfFree γ hγ i⟩

end ModuleCat

end

section

/-!
# Homotopic maps induce the same map on homology

Two homotopic maps of complexes induce the same map on homology in every degree. This is
Mathlib's `Homotopy.homologyMap_eq`, stated for complexes in any preadditive category, which is
tagged directly rather than restated.
-/

add_to_stacks 00LR "Stated for complexes in any preadditive category." Homotopy.homologyMap_eq

end

/-!
# The comparison theorem for resolutions

Fix a commutative ring `R` with `1`, and work in the category of (left) `R`-modules.

We consider nonnegatively graded chain complexes augmented over a module, resolutions,
maps of complexes lifting a map of modules, and chain homotopies. The two main statements
are the classical comparison theorem:

(1) Given a map `φ : M → N`, an (arbitrary) resolution `N_• → N`, and a complex `F_• → M`
    over `M` whose terms are all free `R`-modules, there exists a map of complexes
    `α_• : F_• → N_•` lifting `φ`.

(2) Any two such lifts of the same `φ` are chain homotopic.

## Notes on indexing

The mathematical statement uses `1`-indexed differentials `d_{·,i} : (·)_i → (·)_{i-1}`
for `i ≥ 1`, and the augmentation `ε` sits in "degree `-1`" position. We formalize a
complex as a family of modules `obj : ℕ → Type` together with differentials
`d i : obj (i+1) →ₗ obj i` (so `d i` plays the role of the mathematical `d_{·,i+1}`)
and an augmentation `ε : obj 0 →ₗ M`. With this `0`-indexing:
* `d 0 : obj 1 → obj 0` is the mathematical `d_1`,
* the complex condition `ε ∘ d_1 = 0` becomes `ε ∘ₗ d 0 = 0`,
* the complex condition `d_i ∘ d_{i+1} = 0` becomes `d i ∘ₗ d (i+1) = 0`.
The terms in negative degrees are understood to be `0`; this is reflected by treating
degree `0` separately (e.g. the degree-`0` homotopy relation uses `h_{-1} = 0`).
-/

@[expose] public section

/-- If `e ∘ₗ f = 0` and `d` is exact at `e`, then the range of `f` lies in the range of `d`. -/
private theorem range_le_range_of_exact_of_comp_eq_zero {R : Type*} [CommRing R] {P M N K : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup K] [Module R K] {d : M →ₗ[R] N} {e : N →ₗ[R] K} (h : Function.Exact d e)
    {f : P →ₗ[R] N} (hf : e ∘ₗ f = 0) : LinearMap.range f ≤ LinearMap.range d :=
  (LinearMap.range_le_ker_iff.mpr hf).trans_eq (LinearMap.exact_iff.mp h)

/-- Lifting through the range: if `P` is projective and the range of `g` lies in the
range of `d`, then `g` factors as `d ∘ₗ β`. -/
@[sga "5 XV 3.Lemma3" "more general"]
theorem lift_thru_range {R : Type*} [CommRing R] {P M N : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R P]
    (g : P →ₗ[R] N) (d : M →ₗ[R] N) (h : LinearMap.range g ≤ LinearMap.range d) :
    ∃ β : P →ₗ[R] M, d ∘ₗ β = g := by
  let g' : P →ₗ[R] LinearMap.range d :=
    g.codRestrict (LinearMap.range d) fun x => h (LinearMap.mem_range_self g x)
  obtain ⟨β, hβ⟩ := Module.projective_lifting_property d.rangeRestrict g'
    (LinearMap.surjective_rangeRestrict d)
  refine ⟨β, ?_⟩
  ext x
  simpa [g', LinearMap.codRestrict, LinearMap.rangeRestrict] using
    congrArg Subtype.val (LinearMap.congr_fun hβ x)
universe u

variable {R : Type u} [CommRing R]

/-- A *complex over `M`* is a family of
`R`-modules `obj i` (`i : ℕ`, with `obj i = 0` understood for `i < 0`), differentials
`d i : obj (i+1) →ₗ obj i`, and an augmentation `ε : obj 0 →ₗ M`, satisfying the complex
conditions `ε ∘ₗ d 0 = 0` (i.e. `ε ∘ d_1 = 0`) and `d i ∘ₗ d (i+1) = 0` (i.e.
`d_i ∘ d_{i+1} = 0` for all `i ≥ 1`). -/
structure ComplexOver (R : Type u) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] where
  /-- The term in degree `i`. -/
  obj : ℕ → Type u
  /-- The additive group structure on each term. -/
  [addCommGroup : ∀ i, AddCommGroup (obj i)]
  /-- The `R`-module structure on each term. -/
  [module : ∀ i, Module R (obj i)]
  /-- The differential `d i : obj (i+1) → obj i`, the mathematical `d_{i+1}`. -/
  d : ∀ i, obj (i + 1) →ₗ[R] obj i
  /-- The augmentation `obj 0 → M`. -/
  ε : obj 0 →ₗ[R] M
  /-- The complex condition `ε ∘ d_1 = 0`. -/
  augmentation_comp : ε ∘ₗ d 0 = 0
  /-- The complex condition `d_i ∘ d_{i+1} = 0`. -/
  d_comp_d : ∀ i, d i ∘ₗ d (i + 1) = 0

attribute [instance] ComplexOver.addCommGroup ComplexOver.module

/-- A complex over `N` is a *resolution of `N`* if its
augmented sequence `… → N_1 → N_0 → N → 0` is exact:
* the augmentation `ε` is surjective (exactness at `N`),
* `ker ε = range (d 0)` (exactness at `N_0`), encoded as `Function.Exact (d 0) ε`,
* `ker (d i) = range (d (i+1))` for all `i ≥ 0` (exactness at `N_{i+1}`), encoded as
  `Function.Exact (d (i+1)) (d i)`.
(No freeness or projectivity of the terms is assumed.) -/
@[ega "0 11.4.1" "special case", ega "IV 2.1.10"]
structure IsResolution {N : Type*} [AddCommGroup N] [Module R N]
    (C : ComplexOver R N) : Prop where
  /-- Exactness at `N`: the augmentation is surjective. -/
  surjective_ε : Function.Surjective C.ε
  /-- Exactness at `N_0`. -/
  exact_zero : Function.Exact (C.d 0) C.ε
  /-- Exactness at `N_{i+1}`. -/
  exact_succ : ∀ i, Function.Exact (C.d (i + 1)) (C.d i)

/-- Given `φ : M →ₗ N`, a complex `F`
over `M` and a complex `C` over `N`, a family `α i : F.obj i →ₗ C.obj i` is a *map of
complexes lifting `φ`* if the bottom square commutes (`ε_N ∘ α_0 = φ ∘ ε_F`) and `α` is a
chain map (`d_{N,i} ∘ α_i = α_{i-1} ∘ d_{F,i}`, here `C.d i ∘ₗ α (i+1) = α i ∘ₗ F.d i`). -/
structure IsLift {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (F : ComplexOver R M) (C : ComplexOver R N)
    (α : ∀ i, F.obj i →ₗ[R] C.obj i) : Prop where
  /-- The bottom square commutes: `ε_N ∘ α_0 = φ ∘ ε_F`. -/
  bottom_square : C.ε ∘ₗ α 0 = φ ∘ₗ F.ε
  /-- `α` commutes with the differentials. -/
  chain_map : ∀ i, C.d i ∘ₗ α (i + 1) = α i ∘ₗ F.d i

/-- Two lifts `α, β : F → C` of `φ` are *homotopic* if
there is a family `h i : F.obj i →ₗ C.obj (i+1)` such that the degree-`0` relation
`α_0 - β_0 = d_{N,1} ∘ h_0` holds (encoded `α 0 - β 0 = C.d 0 ∘ₗ h 0`, using `h_{-1} = 0`)
and, for `i ≥ 1`, `α_i - β_i = d_{N,i+1} ∘ h_i + h_{i-1} ∘ d_{F,i}` holds (encoded, after
shifting the index by one, as
`α (i+1) - β (i+1) = C.d (i+1) ∘ₗ h (i+1) + h i ∘ₗ F.d i`). -/
def HomotopicComplexOver {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : ComplexOver R M) (C : ComplexOver R N)
    (α β : ∀ i, F.obj i →ₗ[R] C.obj i) : Prop :=
  ∃ h : ∀ i, F.obj i →ₗ[R] C.obj (i + 1),
    (α 0 - β 0 = C.d 0 ∘ₗ h 0) ∧
    (∀ i, α (i + 1) - β (i + 1) = C.d (i + 1) ∘ₗ h (i + 1) + h i ∘ₗ F.d i)

/-- A complex `F` is *free* if each of its terms is a free `R`-module. (Only freeness of
the terms of `F` is used; more generally projectivity would suffice.) -/
def IsFreeComplex {M : Type*} [AddCommGroup M] [Module R M] (F : ComplexOver R M) : Prop :=
  ∀ i, Module.Free R (F.obj i)

/-- Each term of a free complex is projective. -/
private theorem projective_of_isFreeComplex {M : Type*} [AddCommGroup M] [Module R M]
    {F : ComplexOver R M} (hF : IsFreeComplex F) (i : ℕ) : Module.Projective R (F.obj i) :=
  have := hF i
  inferInstance

/-- **Statement (1): Existence of a lift.** Let `φ : M → N` be a map of `R`-modules, let
`C` be an (arbitrary) resolution of `N`, and let `F` be a complex over `M` whose terms are
all free `R`-modules. Then there exists a map of complexes `α : F → C` lifting `φ`. -/
@[stacks 00LS "(1)"]
theorem exists_lift_along_resolution {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N]
    (φ : M →ₗ[R] N) (F : ComplexOver R M) (C : ComplexOver R N)
    (hC : IsResolution C) (hF : IsFreeComplex F) :
    ∃ α : ∀ i, F.obj i →ₗ[R] C.obj i, IsLift φ F C α := by
  -- Each term of F is projective.
  have proj := projective_of_isFreeComplex hF
  -- State carried by the recursion: a map together with the proof that the range
  -- of `a ∘ₗ F.d i` lies in the range of `C.d i`.
  let T : ℕ → Type _ := fun i =>
    { a : F.obj i →ₗ[R] C.obj i //
      LinearMap.range (a ∘ₗ F.d i) ≤ LinearMap.range (C.d i) }
  -- Base case: lift `φ ∘ₗ F.ε` through the surjection `C.ε`.
  have hbase : ∃ a0 : F.obj 0 →ₗ[R] C.obj 0, C.ε ∘ₗ a0 = φ ∘ₗ F.ε :=
    Module.projective_lifting_property C.ε (φ ∘ₗ F.ε) hC.surjective_ε
  -- The chosen base map and its property.
  let a0 : F.obj 0 →ₗ[R] C.obj 0 := hbase.choose
  have ha0 : C.ε ∘ₗ a0 = φ ∘ₗ F.ε := hbase.choose_spec
  -- `range (a0 ∘ₗ F.d 0) ≤ range (C.d 0)`.
  have hout0 : LinearMap.range (a0 ∘ₗ F.d 0) ≤ LinearMap.range (C.d 0) := by
    refine range_le_range_of_exact_of_comp_eq_zero hC.exact_zero ?_
    rw [← LinearMap.comp_assoc, ha0, LinearMap.comp_assoc, F.augmentation_comp, LinearMap.comp_zero]
  -- The step function: from level `n` produce level `n+1`.
  let step : ∀ n, T n → T (n + 1) := by
    intro n s
    have hex := lift_thru_range (s.val ∘ₗ F.d n) (C.d n) s.property
    refine ⟨hex.choose, ?_⟩
    refine range_le_range_of_exact_of_comp_eq_zero (hC.exact_succ n) ?_
    rw [← LinearMap.comp_assoc, hex.choose_spec, LinearMap.comp_assoc, F.d_comp_d n,
      LinearMap.comp_zero]
  -- Build the sequence by recursion.
  let seq : ∀ n, T n := fun n => Nat.rec (⟨a0, hout0⟩ : T 0) (fun m s => step m s) n
  -- The bottom square is `ha0`; in the chain map condition `seq (i+1) = step i (seq i)`,
  -- whose first component satisfies the spec.
  exact ⟨fun i => (seq i).val, ha0, fun i =>
    (lift_thru_range ((seq i).val ∘ₗ F.d i) (C.d i) (seq i).property).choose_spec⟩

/-- **Statement (2): Uniqueness up to homotopy.** Any two maps of complexes `α, β : F → C`
lifting the same `φ` are chain homotopic. -/
@[stacks 00LS "(2)", ega "III 6.3.8" "partial"]
theorem lift_unique_up_to_homotopy {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (F : ComplexOver R M) (C : ComplexOver R N)
    (hC : IsResolution C) (hF : IsFreeComplex F)
    (α β : ∀ i, F.obj i →ₗ[R] C.obj i)
    (hα : IsLift φ F C α) (hβ : IsLift φ F C β) :
    HomotopicComplexOver F C α β := by
  have proj := projective_of_isFreeComplex hF
  -- The difference, a chain map lifting `0`.
  let γ : ∀ i, F.obj i →ₗ[R] C.obj i := fun i => α i - β i
  have hγ0 : C.ε ∘ₗ γ 0 = 0 := by
    show C.ε ∘ₗ (α 0 - β 0) = 0
    rw [LinearMap.comp_sub, hα.bottom_square, hβ.bottom_square, sub_self]
  have hγchain : ∀ i, C.d i ∘ₗ γ (i + 1) = γ i ∘ₗ F.d i := by
    intro i
    show C.d i ∘ₗ (α (i + 1) - β (i + 1)) = (α i - β i) ∘ₗ F.d i
    rw [LinearMap.comp_sub, hα.chain_map, hβ.chain_map, LinearMap.sub_comp]
  -- State carried by the recursion: a homotopy term `h i` with the property that
  -- `C.d i ∘ₗ h i ∘ₗ F.d i = γ i ∘ₗ F.d i`.
  let S : ℕ → Type _ := fun i =>
    { hi : F.obj i →ₗ[R] C.obj (i + 1) //
      C.d i ∘ₗ (hi ∘ₗ F.d i) = γ i ∘ₗ F.d i }
  -- Base case at level 0: lift `γ 0` through `C.d 0`.
  have hbase : ∃ h0 : F.obj 0 →ₗ[R] C.obj 1, C.d 0 ∘ₗ h0 = γ 0 :=
    lift_thru_range (γ 0) (C.d 0)
      (range_le_range_of_exact_of_comp_eq_zero hC.exact_zero hγ0)
  let h0 : F.obj 0 →ₗ[R] C.obj 1 := hbase.choose
  have hh0 : C.d 0 ∘ₗ h0 = γ 0 := hbase.choose_spec
  have hP0 : C.d 0 ∘ₗ (h0 ∘ₗ F.d 0) = γ 0 ∘ₗ F.d 0 := by
    rw [← LinearMap.comp_assoc, hh0]
  -- The range condition needed for the lifting at each step.
  have hrange : ∀ (n : ℕ) (s : S n),
      LinearMap.range (γ (n + 1) - s.val ∘ₗ F.d n) ≤ LinearMap.range (C.d (n + 1)) := by
    intro n s
    refine range_le_range_of_exact_of_comp_eq_zero (hC.exact_succ n) ?_
    rw [LinearMap.comp_sub, hγchain n, s.property, sub_self]
  -- The chosen successor homotopy term and its defining equation.
  let nextMap : ∀ (n : ℕ) (s : S n), F.obj (n + 1) →ₗ[R] C.obj (n + 2) := fun n s =>
    (lift_thru_range (γ (n + 1) - s.val ∘ₗ F.d n) (C.d (n + 1)) (hrange n s)).choose
  have nextSpec : ∀ (n : ℕ) (s : S n),
      C.d (n + 1) ∘ₗ nextMap n s = γ (n + 1) - s.val ∘ₗ F.d n := fun n s =>
    (lift_thru_range (γ (n + 1) - s.val ∘ₗ F.d n) (C.d (n + 1)) (hrange n s)).choose_spec
  -- Step function.
  let step : ∀ n, S n → S (n + 1) := fun n s =>
    ⟨nextMap n s, by
      rw [← LinearMap.comp_assoc, nextSpec n s]
      rw [LinearMap.sub_comp, LinearMap.comp_assoc, F.d_comp_d n]
      simp⟩
  let seq : ∀ n, S n := fun n => Nat.rec (⟨h0, hP0⟩ : S 0) (fun m s => step m s) n
  let h : ∀ i, F.obj i →ₗ[R] C.obj (i + 1) := fun i => (seq i).val
  -- The degree-0 relation is `hh0`, and the general one is `nextSpec`.
  exact ⟨h, hh0.symm, fun i => sub_eq_iff_eq_add.mp (nextSpec i (seq i)).symm⟩

end
