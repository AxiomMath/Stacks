module

import StacksFrontier.RingTheory.FinitePresentation.ModuleDescent
public import StacksFrontier.Algebra.MittagLeffler.Defs
public import StacksFrontier.RingTheory.Module.Factorization
public import StacksFrontier.Algebra.MittagLeffler.TensorProduct

@[expose] public section

universe v

universe u w

/-!
# The equivalent forms of the Mittag-Leffler condition on a directed system

Let `R` be a commutative ring, let `F : J ⥤ ModuleCat R` be a directed system `(M i, f i j)` of
finitely presented `R`-modules over a nonempty directed preorder `J`, and let `c` be a colimit
cocone on `F`, so that `M = c.pt` is `colim_i M i` with canonical maps `f i = c.ι.app i`. This file
proves Stacks 059E: the five conditions (1)-(5) of the tag are equivalent.

The route is the source's, and the hard implication is `(1) ⟹ (2)`. All of its content is
`Stacks.MittagLeffler.SystemCriterion.exists_map_eq_comp`: if `f i` factors through a map
`g : M i → Q` with `Q` of finite presentation — which is what (1) provides, once 059D has turned
the domination of `f i` by `g` into a factorization — then some transition map `f i l` factors
through `g`, and therefore dominates `f i`. `(2) ⟹ (1)`: a map from a finitely presented module
factors as `f = f i ∘ g'`, and
`g = f i j ∘ g'` works, domination being stable under precomposition. `(2) ⟺ (3)`: 059D converts
domination into factorization one way, and the other way `Ker(f i ⊗ id_T)` is the union of the
`Ker(f i k ⊗ id_T)`. `(3) ⟹ (4)` is the definition of the Mittag-Leffler condition on the dual
systems, `(4) ⟹ (5)` is a specialization, and `(5) ⟹ (3)` is read off the `j`-th component of
`∏_s M s`, the inclusion `Pi.single` being split by the projection.

## Main results

* `Stacks.MittagLeffler.SystemCriterion.solution`: the statement of Stacks 059E,
  `CategoryTheory.Functor.tfae_isMittagLefflerSystem`.

## Implementation notes

The facts about a filtered colimit of modules used here are proved as private lemmas, `Mathlib`
having them only for a diagram whose members lie in the universe of the ring, where the
filtered-colimit API of `ModuleCat` is stated, while the modules here live in an arbitrary
universe `w` with `R` merely `w`-small. All of them come from one comparison,
`Stacks.MittagLeffler.SystemCriterion.exists_linearEquiv_directLimit`, of `c` with
`ModuleCat.directLimitCocone`, which is
universe-polymorphic: an element of the colimit comes from a member, an element of a member which
dies in the colimit dies at a later stage, and — via `TensorProduct.directLimitLeft`, that
tensoring commutes with a direct limit — the same after tensoring with a fixed module.

`Stacks.MittagLeffler.SystemCriterion.exists_comp_eq_of_finitePresentation` and
`Stacks.MittagLeffler.SystemCriterion.exists_map_comp_eq_of_comp_ι_eq` together say that a finitely
presented module is a finitely presentable object of `ModuleCat R`: a map from it into the colimit
factors through a stage, and two maps into a member which agree in the colimit agree after a
transition map. Both rest on `Stacks.MittagLeffler.SystemCriterion.exists_map_eq_zero_of_fg`, that
a finitely generated submodule of the kernel of a leg of the cocone is killed by a transition map.

`Stacks.FinitePresentation.ModuleDescent.exists_comp_eq_of_ker_le_ker`, that a linear map killing
the kernel of a surjection factors through it, and
`Stacks.MittagLeffler.SystemCriterion.exists_surjective_fin`, that a finitely presented module is
the quotient of a finite free module by a finitely generated submodule, are stated in the
generality they hold in; neither is in `Mathlib`, which has the second only in the equivalent form
`Module.FinitePresentation.exists_fin`, as an isomorphism with a quotient.

## References

* [StacksProject 059E](https://stacks.math.columbia.edu/tag/059E)
-/



open CategoryTheory Limits
open scoped TensorProduct

namespace Stacks.MittagLeffler.SystemCriterion

/-! ### Generalities on a system of modules over a preorder -/

section Preorder

variable {R : Type u} [CommRing R] {J : Type w} [Preorder J] {F : J ⥤ ModuleCat.{w} R}

/-- Two composites of transition maps with the same source and target agree: between two objects of
the index category of a preorder there is at most one arrow. -/
private theorem map_eq_comp {i j k : J} (u : i ⟶ j) (v : j ⟶ k) (w : i ⟶ k) :
    F.map w = F.map u ≫ F.map v := by
  rw [← F.map_comp]; congr 1

/-- A leg of a cocone absorbs the transition maps. -/
private theorem ι_app_map (c : Cocone F) {i j : J} (u : i ⟶ j) (y : F.obj i) :
    c.ι.app j (F.map u y) = c.ι.app i y := congr($(c.w u) y)

/-- `F`, read as an unbundled directed system of `R`-modules. -/
private theorem directedSystem_map (F : J ⥤ ModuleCat.{w} R) :
    DirectedSystem (fun i => (F.obj i : Type w)) fun _ _ h => (F.map (homOfLE h)).hom := by
  refine ⟨fun _ y => by simp, fun _ _ _ hij hjk y => ?_⟩
  exact (congr($(map_eq_comp (F := F) (homOfLE hij) (homOfLE hjk)
    (homOfLE (hij.trans hjk))) y)).symm

end Preorder

/-! ### Domination -/

section Domination

variable {R : Type u} [CommRing R]

/-- The kernel of a tensored composite is the preimage of the kernel of its second factor. -/
private theorem ker_rTensor_comp {A B E : ModuleCat.{w} R} (e : E ⟶ A) (a : A ⟶ B)
    (T : ModuleCat.{w} R) :
    LinearMap.ker ((e ≫ a).hom.rTensor T) =
      (LinearMap.ker (a.hom.rTensor T)).comap (e.hom.rTensor T) := by
  rw [ModuleCat.hom_comp, LinearMap.rTensor_comp, LinearMap.ker_comp]

/-- A map which factors through another is dominated by it: `a = b ≫ h` implies that `a ⊗ id_T`
kills whatever `b ⊗ id_T` kills. -/
private theorem ker_rTensor_le_of_eq_comp {A B D : ModuleCat.{w} R} {a : A ⟶ B} {b : A ⟶ D}
    {h : D ⟶ B} (hab : a = b ≫ h) (T : ModuleCat.{w} R) :
    LinearMap.ker (b.hom.rTensor T) ≤ LinearMap.ker (a.hom.rTensor T) := by
  rw [hab, ModuleCat.hom_comp, LinearMap.rTensor_comp]
  exact LinearMap.ker_le_ker_comp _ _

/-- Domination is stable under precomposition. -/
private theorem ker_rTensor_comp_le_of_ker_rTensor_le {A B D E : ModuleCat.{w} R} (e : E ⟶ A)
    {a : A ⟶ B} {b : A ⟶ D} (T : ModuleCat.{w} R)
    (h : LinearMap.ker (a.hom.rTensor T) ≤ LinearMap.ker (b.hom.rTensor T)) :
    LinearMap.ker ((e ≫ a).hom.rTensor T) ≤ LinearMap.ker ((e ≫ b).hom.rTensor T) := by
  rw [ker_rTensor_comp, ker_rTensor_comp]
  exact Submodule.comap_mono h

/-- **Stacks 059D** for modules of finite presentation, whose hypothesis on the cokernel is then
automatic: a map `g : A ⟶ D` dominated by `f : A ⟶ B` factors through `f`. -/
private theorem exists_eq_comp_of_forall_ker_rTensor_le [Small.{w} R] {A B D : ModuleCat.{w} R}
    [Module.Finite R A] [Module.FinitePresentation R B] (f : A ⟶ B) (g : A ⟶ D)
    (h : ∀ T : ModuleCat.{w} R,
      LinearMap.ker (f.hom.rTensor T) ≤ LinearMap.ker (g.hom.rTensor T)) :
    ∃ k : B ⟶ D, g = f ≫ k := by
  have : Module.FinitePresentation R ((B : Type w) ⧸ LinearMap.range f.hom) :=
    Module.finitePresentation_of_surjective (LinearMap.range f.hom).mkQ
      (Submodule.mkQ_surjective _) (by rw [Submodule.ker_mkQ]; exact Submodule.fg_range _)
  obtain ⟨k, hk⟩ := (LinearMap.forall_ker_rTensor_le_iff_exists_eq_comp f.hom g.hom).1
    fun T _ _ => h (ModuleCat.of R T)
  exact ⟨ModuleCat.ofHom k, ModuleCat.hom_ext hk⟩

end Domination

/-! ### Presenting a finitely presented module -/

section Presentation

variable {R : Type u} [CommRing R]

/-- A finitely presented module is the quotient of a finite free module by a finitely generated
submodule. -/
private theorem exists_surjective_fin (P : Type w) [AddCommGroup P] [Module R P]
    [Module.FinitePresentation R P] :
    ∃ (n : ℕ) (π : (Fin n → R) →ₗ[R] P), Function.Surjective π ∧ (LinearMap.ker π).FG := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R P
  refine ⟨n, e.symm.toLinearMap ∘ₗ K.mkQ, e.symm.surjective.comp K.mkQ_surjective, ?_⟩
  rwa [LinearMap.ker_comp_of_ker_eq_bot _ e.symm.ker, Submodule.ker_mkQ]

end Presentation

/-! ### A filtered colimit of modules

`Mathlib`'s filtered-colimit API for `ModuleCat R` is stated for diagrams in the universe of `R`;
the facts below are the ones needed here, for a diagram in an arbitrary universe `w`, and all of
them are read off `exists_linearEquiv_directLimit`. -/

section Colimit

variable {R : Type u} [CommRing R] {J : Type w} [Preorder J] [IsDirectedOrder J]
  {F : J ⥤ ModuleCat.{w} R} {c : Cocone F}

/-- Any finite family of indices of a directed preorder has an upper bound which also dominates a
prescribed index. -/
private theorem exists_ub {n : ℕ} (kk : Fin n → J) (i : J) : ∃ l : J, i ≤ l ∧ ∀ t, kk t ≤ l := by
  classical
  have : Nonempty J := ⟨i⟩
  obtain ⟨l, hl⟩ := Finset.exists_le (insert i (Finset.univ.image kk))
  exact ⟨l, hl i (by simp), fun t => hl _ (by simp)⟩

omit [IsDirectedOrder J] in
/-- The colimit of a directed system of modules is its unbundled `Module.DirectLimit`, compatibly
with the legs of the cocone. -/
private theorem exists_linearEquiv_directLimit [DecidableEq J] (hc : IsColimit c) :
    ∃ e : (c.pt : Type w) ≃ₗ[R] Module.DirectLimit (fun i => (F.obj i : Type w))
        (fun _ _ h => (F.map (homOfLE h)).hom),
      ∀ (i : J) (y : F.obj i), e (c.ι.app i y) = Module.DirectLimit.of R J _ _ i y := by
  have := directedSystem_map F
  have hd : @IsColimit J _ (ModuleCat.{w} R) _ F
      (ModuleCat.directLimitCocone (fun i => (F.obj i : Type w))
        (fun _ _ h => (F.map (homOfLE h)).hom)) :=
    ModuleCat.directLimitIsColimit _ _
  exact ⟨(hc.coconePointUniqueUpToIso hd).toLinearEquiv,
    fun i y => congr($(hc.comp_coconePointUniqueUpToIso_hom hd i) y)⟩

/-- The legs of a colimit cocone of a directed system of modules are jointly surjective. -/
private theorem exists_ι_app_eq [Nonempty J] (hc : IsColimit c) (x : c.pt) :
    ∃ (i : J) (y : F.obj i), c.ι.app i y = x := by
  classical
  obtain ⟨e, he⟩ := exists_linearEquiv_directLimit hc
  obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of (e x)
  exact ⟨i, y, e.injective ((he i y).trans hy)⟩

/-- An element of a member of a directed system which is killed by its leg into the colimit is
killed by some transition map. -/
private theorem exists_map_eq_zero (hc : IsColimit c) (i : J) (y : F.obj i)
    (hy : c.ι.app i y = 0) : ∃ (k : J) (v : i ⟶ k), (F.map v) y = 0 := by
  classical
  have := directedSystem_map F
  obtain ⟨e, he⟩ := exists_linearEquiv_directLimit hc
  obtain ⟨k, hik, hk⟩ := Module.DirectLimit.of.zero_exact
    (show Module.DirectLimit.of R J (fun i => (F.obj i : Type w))
        (fun _ _ h => (F.map (homOfLE h)).hom) i y = 0 by rw [← he i y, hy, map_zero])
  exact ⟨k, homOfLE hik, hk⟩

/-- `Ker(f i)` is the union of the kernels of the transition maps out of `i`, in the strong form: a
finitely generated submodule of `Ker(f i)` is killed by a single transition map. -/
private theorem exists_map_eq_zero_of_fg (hc : IsColimit c) {i : J} {N : Submodule R (F.obj i)}
    (hN : N.FG) (hNc : N ≤ LinearMap.ker (c.ι.app i).hom) :
    ∃ (k : J) (v : i ⟶ k), N ≤ LinearMap.ker (F.map v).hom := by
  classical
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hN
  choose kk vv hvv using fun t => exists_map_eq_zero hc i (s t)
    (hNc (hs.le (Submodule.subset_span ⟨t, rfl⟩)))
  obtain ⟨l, hil, hkl⟩ := exists_ub kk i
  refine ⟨l, homOfLE hil, hs ▸ Submodule.span_le.2 ?_⟩
  rintro x ⟨t, rfl⟩
  have := congr($(map_eq_comp (F := F) (vv t) (homOfLE (hkl t)) (homOfLE hil)) (s t))
  simp only [SetLike.mem_coe, LinearMap.mem_ker, this, ModuleCat.comp_apply, hvv t, map_zero]

/-- The kernel of `f i ⊗ id_T` is the union of the kernels of the `f i k ⊗ id_T`. This is
`TensorProduct.directLimitLeft`, that tensoring commutes with a direct limit, transported along
the comparison of `c` with `ModuleCat.directLimitCocone`. -/
private theorem exists_map_rTensor_eq_zero (hc : IsColimit c) (T : ModuleCat.{w} R) (i : J)
    (x : F.obj i ⊗[R] T) (hx : (c.ι.app i).hom.rTensor T x = 0) :
    ∃ (k : J) (v : i ⟶ k), (F.map v).hom.rTensor T x = 0 := by
  classical
  have := directedSystem_map F
  obtain ⟨e, he⟩ := exists_linearEquiv_directLimit hc
  have h0 : (Module.DirectLimit.of R J (fun i => (F.obj i : Type w))
      (fun _ _ h => (F.map (homOfLE h)).hom) i).rTensor (T : Type w) x = 0 := by
    rw [show Module.DirectLimit.of R J _ _ i = (e : (c.pt : Type w) →ₗ[R] _) ∘ₗ (c.ι.app i).hom from
      LinearMap.ext fun y => (he i y).symm, LinearMap.rTensor_comp_apply, hx, map_zero]
  have h1 := TensorProduct.directLimitLeft_rTensor_of
    (fun _ _ h => (F.map (homOfLE h)).hom) (T : Type w) x
  rw [h0, map_zero] at h1
  obtain ⟨k, hik, hk⟩ := Module.DirectLimit.of.zero_exact h1.symm
  exact ⟨k, homOfLE hik, hk⟩

/-- A map from a finite free module to the colimit factors through a stage. -/
private theorem exists_comp_eq_of_free [Nonempty J] (hc : IsColimit c) {n : ℕ}
    (g : (Fin n → R) →ₗ[R] (c.pt : Type w)) :
    ∃ (k : J) (φ : (Fin n → R) →ₗ[R] (F.obj k : Type w)), (c.ι.app k).hom ∘ₗ φ = g := by
  classical
  choose ii y hy using fun t => exists_ι_app_eq hc (g (Pi.basisFun R (Fin n) t))
  obtain ⟨k, -, hkk⟩ := exists_ub ii (Classical.arbitrary J)
  refine ⟨k, (Pi.basisFun R (Fin n)).constr ℕ fun t => F.map (homOfLE (hkk t)) (y t),
    (Pi.basisFun R (Fin n)).ext fun t => ?_⟩
  simpa [Module.Basis.constr_basis] using
    (ι_app_map c (homOfLE (hkk t)) (y t)).trans (hy t)

/-- A map from a finitely presented module to the colimit factors through a stage. -/
private theorem exists_comp_eq_of_finitePresentation [Nonempty J] (hc : IsColimit c)
    (P : ModuleCat.{w} R) [Module.FinitePresentation R P] (g : P ⟶ c.pt) :
    ∃ (k : J) (h : P ⟶ F.obj k), h ≫ c.ι.app k = g := by
  obtain ⟨n, π, hπ, hK⟩ := exists_surjective_fin (R := R) (P : Type w)
  obtain ⟨k, φ, hφ⟩ := exists_comp_eq_of_free hc (g.hom ∘ₗ π)
  obtain ⟨l, v, hv⟩ := exists_map_eq_zero_of_fg hc (N := (LinearMap.ker π).map φ) (hK.map φ)
    (by
      rintro _ ⟨z, hz, rfl⟩
      refine LinearMap.mem_ker.2 ?_
      have h1 := LinearMap.congr_fun hφ z
      rwa [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.1 hz, map_zero] at h1)
  obtain ⟨h, hh⟩ := Stacks.FinitePresentation.ModuleDescent.exists_comp_eq_of_ker_le_ker _ hπ
    ((F.map v).hom ∘ₗ φ)
    (by rw [LinearMap.ker_comp]; exact Submodule.map_le_iff_le_comap.1 hv)
  refine ⟨l, ModuleCat.ofHom h, ModuleCat.hom_ext (LinearMap.ext ?_)⟩
  refine hπ.forall.2 fun z => ?_
  have h1 : h (π z) = F.map v (φ z) := congr($hh z)
  simpa [h1, ι_app_map c v (φ z)] using LinearMap.congr_fun hφ z

/-- Two maps from a finitely generated module into a member of the system which agree in the
colimit agree after some transition map. -/
private theorem exists_map_comp_eq_of_comp_ι_eq (hc : IsColimit c) {P : ModuleCat.{w} R}
    [Module.Finite R P] {i : J} (a b : P ⟶ F.obj i) (hab : a ≫ c.ι.app i = b ≫ c.ι.app i) :
    ∃ (k : J) (v : i ⟶ k), a ≫ F.map v = b ≫ F.map v := by
  obtain ⟨k, v, hv⟩ := exists_map_eq_zero_of_fg hc (N := LinearMap.range (a.hom - b.hom))
    (Submodule.fg_range _) (by
      rintro _ ⟨z, rfl⟩
      simpa [sub_eq_zero] using congr($hab z))
  refine ⟨k, v, ModuleCat.hom_ext (LinearMap.ext fun z => ?_)⟩
  have := LinearMap.mem_ker.1 (hv ⟨z, rfl⟩)
  simp only [LinearMap.sub_apply, map_sub, sub_eq_zero] at this
  simpa using this

end Colimit

/-! ### The heart of `(1) ⟹ (2)` -/

section Heart

variable {R : Type u} [CommRing R] {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  {F : J ⥤ ModuleCat.{w} R} [∀ i, Module.FinitePresentation R (F.obj i)] {c : Cocone F}

/-- If the canonical map `f i : M i → M` factors through a map `g : M i → Q` whose target is of
finite presentation, then some transition map out of `i` factors through `g`. Indeed `Q → M`
factors through some `M j` because `Q` is of finite presentation, and the two resulting maps
`M i → M j` agree in `M`, hence agree after a transition map. -/
private theorem exists_map_eq_comp (hc : IsColimit c) {i : J} {Q : ModuleCat.{w} R}
    [Module.FinitePresentation R Q] {g : F.obj i ⟶ Q} {k : Q ⟶ c.pt} (hk : c.ι.app i = g ≫ k) :
    ∃ (l : J) (u : i ⟶ l) (h : Q ⟶ F.obj l), F.map u = g ≫ h := by
  obtain ⟨j, h, hh⟩ := exists_comp_eq_of_finitePresentation hc Q k
  obtain ⟨m, him, hjm⟩ := IsDirected.directed (r := (· ≤ ·)) i j
  obtain ⟨l, v, hv⟩ := exists_map_comp_eq_of_comp_ι_eq hc
    (g ≫ h ≫ F.map (homOfLE hjm)) (F.map (homOfLE him))
    (by simp only [Category.assoc, c.w, hh]; exact hk.symm)
  exact ⟨l, homOfLE him ≫ v, h ≫ F.map (homOfLE hjm) ≫ F.map v, by
    rw [F.map_comp, ← hv]; simp⟩

end Heart

/-- Stacks 059E: for a directed system `F` of finitely presented `R`-modules with colimit cocone
`c`, the following are equivalent: (1) every map from a finitely presented module to `c.pt` has the
same kernels after tensoring as some map into a finitely presented module; (2) every leg `f i` of
the cocone is dominated by some transition map `F.map u` out of `i`; (3) for every `i` there is a
transition map `F.map u : M i → M j` that factors through every transition map `F.map v` out of
`i`; (4) `F` satisfies the Mittag-Leffler condition `F.IsMittagLefflerSystem`; (5) the inverse
system `Hom(M i, ∏ s, M s)` is Mittag-Leffler. -/
public theorem solution {R : Type u} [CommRing R] [Small.{w} R] {J : Type w}
    [Preorder J] [IsDirectedOrder J] [Nonempty J] (F : J ⥤ ModuleCat.{w} R)
    [∀ i, Module.FinitePresentation R (F.obj i)] {c : Cocone F} (hc : IsColimit c) :
    List.TFAE
      [∀ (P : ModuleCat.{w} R) [Module.FinitePresentation R P] (f : P ⟶ c.pt),
          ∃ (Q : ModuleCat.{w} R) (_ : Module.FinitePresentation R Q) (g : P ⟶ Q),
            ∀ T : ModuleCat.{w} R,
              LinearMap.ker (f.hom.rTensor T) = LinearMap.ker (g.hom.rTensor T),
        ∀ i : J, ∃ (j : J) (u : i ⟶ j), ∀ T : ModuleCat.{w} R,
          LinearMap.ker ((c.ι.app i).hom.rTensor T) ≤ LinearMap.ker ((F.map u).hom.rTensor T),
        ∀ i : J, ∃ (j : J) (u : i ⟶ j), ∀ (k : J) (v : i ⟶ k),
          ∃ h : F.obj k ⟶ F.obj j, F.map u = F.map v ≫ h,
        F.IsMittagLefflerSystem,
        (F.op ⋙ yoneda.obj (ModuleCat.of R (∀ s : J, F.obj s))).IsMittagLeffler] := by
  classical
  tfae_have 1 → 2 := by
    intro h1 i
    obtain ⟨Q, _, g, hg⟩ := h1 (F.obj i) (c.ι.app i)
    obtain ⟨k, hk⟩ := exists_eq_comp_of_forall_ker_rTensor_le g (c.ι.app i) fun T => (hg T).ge
    obtain ⟨l, u, h, hh⟩ := exists_map_eq_comp hc hk
    exact ⟨l, u, fun T => (hg T).le.trans (ker_rTensor_le_of_eq_comp hh T)⟩
  tfae_have 2 → 1 := by
    intro h2 P _ f
    obtain ⟨i, g, hg⟩ := exists_comp_eq_of_finitePresentation hc P f
    obtain ⟨j, u, hu⟩ := h2 i
    refine ⟨F.obj j, inferInstance, g ≫ F.map u, fun T => le_antisymm ?_ ?_⟩
    · exact hg ▸ ker_rTensor_comp_le_of_ker_rTensor_le g T (hu T)
    · exact ker_rTensor_le_of_eq_comp (by rw [Category.assoc, c.w, hg]) T
  tfae_have 2 → 3 := by
    intro h2 i
    obtain ⟨j, u, hu⟩ := h2 i
    exact ⟨j, u, fun k v => exists_eq_comp_of_forall_ker_rTensor_le (F.map v) (F.map u)
      fun T => (ker_rTensor_le_of_eq_comp (c.w v).symm T).trans (hu T)⟩
  tfae_have 3 → 2 := by
    intro h3 i
    obtain ⟨j, u, hu⟩ := h3 i
    refine ⟨j, u, fun T x hx => ?_⟩
    obtain ⟨k, v, hv⟩ := exists_map_rTensor_eq_zero hc T i x (LinearMap.mem_ker.1 hx)
    obtain ⟨h, hh⟩ := hu k v
    simp only [LinearMap.mem_ker, hh, ModuleCat.hom_comp, LinearMap.rTensor_comp,
      LinearMap.coe_comp, Function.comp_apply, hv, map_zero]
  tfae_have 3 → 4 := by
    intro h3
    refine ⟨fun j => inferInstance, fun N jo => ?_⟩
    obtain ⟨i₀⟩ := jo
    obtain ⟨j₀, u, hu⟩ := h3 i₀
    refine ⟨Opposite.op j₀, u.op, fun ko g => ?_⟩
    rintro x ⟨ψ, rfl⟩
    obtain ⟨h, hh⟩ := hu ko.unop g.unop
    refine ⟨h ≫ ψ, ?_⟩
    simp only [Functor.comp_map, Functor.op_map, yoneda_obj_map, Quiver.Hom.unop_op]
    rw [hh]
    simp
  tfae_have 4 → 5 := fun h4 => h4.2 _
  tfae_have 5 → 3 := by
    intro h5 i₀
    obtain ⟨jo, fo, hml⟩ := h5 (Opposite.op i₀)
    obtain ⟨j₀⟩ := jo
    refine ⟨j₀, fo.unop, fun k₀ v => ?_⟩
    set ψ : F.obj j₀ ⟶ ModuleCat.of R (∀ s : J, (F.obj s : Type w)) :=
      ModuleCat.ofHom (LinearMap.single R (fun s : J => (F.obj s : Type w)) j₀)
    set p : ModuleCat.of R (∀ s : J, (F.obj s : Type w)) ⟶ F.obj j₀ :=
      ModuleCat.ofHom (LinearMap.proj (R := R) (φ := fun s : J => (F.obj s : Type w)) j₀)
    have hψp : ψ ≫ p = 𝟙 (F.obj j₀) :=
      ModuleCat.hom_ext (LinearMap.proj_comp_single_same R (fun s : J => (F.obj s : Type w)) j₀)
    obtain ⟨χ, hχ⟩ := hml v.op ⟨ψ, rfl⟩
    refine ⟨χ ≫ p, ?_⟩
    rw [← Category.assoc, show F.map v ≫ χ = F.map fo.unop ≫ ψ from hχ, Category.assoc, hψp,
      Category.comp_id]
  tfae_finish

end Stacks.MittagLeffler.SystemCriterion

/-!
# The equivalent forms of the Mittag-Leffler condition on a directed system

Let `R` be a commutative ring, let `(M i, f i j)` be a directed system of finitely presented
`R`-modules indexed by a directed preorder `J` — that is, a functor `F : J ⥤ ModuleCat R` — and
let `M = colim_{i ∈ J} M i`, with canonical maps `f i : M i → M`. Following the source, a map
`g : P → Q` *dominates* a map `f : P → N` if `Ker(f ⊗ id_T) ⊆ Ker(g ⊗ id_T)` for every `R`-module
`T` (Definition 059B); factorization implies domination, and for `f` with finitely presented
cokernel the two agree (Lemma 059D). Dualizing the system into an `R`-module `T` turns it into an
inverse system `(Hom_R(M i, T), Hom_R(f i j, T))`, and the system is a *Mittag-Leffler system*
when all of those are Mittag-Leffler (Definition 059A).

Five conditions are then equivalent:

1. every map `f : P → M` from a finitely presented module dominates and is dominated by some
   map `g : P → Q` into a finitely presented module;
2. for each `i` some transition map `f i j`, `j ≥ i`, dominates the canonical map
   `f i : M i → M`;
3. for each `i` some transition map `f i j`, `j ≥ i`, factors through `f i k` for all `k ≥ i`;
4. `F` is a Mittag-Leffler system, that is `(Hom_R(M i, T), Hom_R(f i j, T))` is a
   Mittag-Leffler inverse system for every `R`-module `T`;
5. the same for the single test module `T = ∏_{s ∈ J} M s`.

Condition (1) mentions only `M`, so it is a property of the module `M` alone: it is the
definition of a *Mittag-Leffler module* (Definition 059F). Conditions (2), (3) and (4) say that
the presenting system is one whose dual systems are Mittag-Leffler, and (5) is the finiteness of
the criterion — a single test module suffices.

## Main results

* `CategoryTheory.Functor.tfae_isMittagLefflerSystem`: the five conditions above are equivalent,
  for a directed system of finitely presented `R`-modules with a chosen colimit cocone.

## Implementation notes

Departures from the source's form, none of them weakening it.

The directed system `(M i, f i j)` is a functor `F : J ⥤ ModuleCat R` on a directed preorder `J`,
and "`M = colim M i`" is an arbitrary cocone `c` on `F` together with `IsColimit c`, rather than a
chosen construction of the colimit; `M` is `c.pt` and the canonical map `f i : M i → M` is the leg
`c.ι.app i`. This is what lets conditions (1) and (2) refer to the source's canonical maps rather
than to abstract ones. Transition maps are written `F.map u` for `u : i ⟶ j` in place of `f i j`,
as in 059W.

Condition (4) is `F.IsMittagLefflerSystem` (Definition 059A), whose statement is the conjunction of
the source's condition (4) with finite presentation of the members. The second conjunct is the
standing hypothesis of the proposition, so under that hypothesis this is the source's condition
(4); it is preferred to a re-spelling because it is the notion the section exists to characterize,
"`M` is the colimit of a Mittag-Leffler directed system".

Domination is spelled out, `Mathlib` having no name for it, exactly as in 059D: `f ⊗ id_T` is
`f.hom.rTensor T` and domination is `ker (f.hom.rTensor T) ≤ ker (g.hom.rTensor T)`, while "`f`
and `g` dominate each other" is the equality of those two kernels.

The test modules `T`, the modules `P` and `Q` of condition (1), and the index `J` all live in the
universe `w` of the members of the system, and `R` is `w`-small, as in 059D and 05CQ. For a
`w`-small `R` every finitely presented `R`-module is isomorphic to one in `Type w` and domination
may be tested on finitely presented modules alone (Lemma 059C), so the displayed quantifiers are
the source's quantifiers over all modules. Smallness of `J` is what makes `∏_{s ∈ J} M s` an
object of `ModuleCat.{w} R`, as condition (5) requires; the product is the concrete `∀ s : J, M s`
rather than a categorical product, which pins it to the source's.

Faithfulness. (1) No hypothesis is dead: directedness of `J` is what makes `Ker(f i ⊗ id_T)` the
union of the `Ker(f i k ⊗ id_T)` and what lets a map out of a finitely presented module into `M`
factor through some `M i`, and both are used; `Nonempty J` is the source's convention for a
directed set and is what makes `J` filtered; finite presentation of the members is what makes the
cokernels of the transition maps finitely presented, which is what turns domination into
factorization in the passage from (2) to (3), by Lemma 059D; `Small.{w} R` is what makes the
quantifiers over `Type w` the source's quantifiers over all modules; and `IsColimit c` is what
ties the two conditions on the system, (3) and (4), to the two conditions involving `M`, (1) and
(2). (2) The scalars and the base are the source's: one commutative ring `R` throughout, `F` takes
values in `R`-modules, all tensor products are over `R`, the dual systems are of `R`-module
homomorphisms, and nothing is localized or base changed. (3) The canonical maps are pinned, not
merely asserted to exist: the colimit cocone `c` is part of the data and `f i` is its leg
`c.ι.app i`; the maps whose kernels are compared are `f.hom.rTensor T` and `g.hom.rTensor T`, not
merely maps `P ⊗ T → M ⊗ T` and `P ⊗ T → Q ⊗ T`; the transition maps of the dual inverse systems
are precomposition with the `F.map u`, by the construction of `IsMittagLefflerSystem`; and the
factorization in (3) is pinned by the equation `F.map u = F.map v ≫ h`. Only `Q` and `g` in (1),
the index `j` in (2) and (3), and `h` in (3) are existentially quantified, as they are in the
source. (4) The instantiation is not degenerate: for `J` the finite subsets of a set `S`, `F` the
system of the free modules `R^i` and `M = R^{(S)}` the free module on `S`, all five conditions
hold, (3) with `j = i` because `R^i` is a direct summand of `R^k`; and all five fail for `R = ℤ`
and `M = ℚ` written as the colimit of the directed system of its cyclic subgroups `ℤ · (1 / n !)`,
since `ℚ` is flat and countably generated but not projective (Theorem 059Z). So neither side of
the equivalence is automatic.

## References

* [StacksProject 059E](https://stacks.math.columbia.edu/tag/059E)
-/



open CategoryTheory Limits

@[expose] public section

namespace CategoryTheory.Functor

/-- **Stacks 059E.** Let `R` be a commutative ring, let `F : J ⥤ ModuleCat R` be a directed system
`(M i, f i j)` of finitely presented `R`-modules over a nonempty directed preorder `J`, and let `c`
be a colimit cocone on `F`, so that `M = c.pt` is `colim_{i ∈ J} M i` with canonical maps
`f i : M i → M`. The following are equivalent:

1. for every finitely presented `R`-module `P` and every map `f : P → M` there are a finitely
   presented `R`-module `Q` and a map `g : P → Q` which dominate each other, that is
   `Ker(f ⊗ id_T) = Ker(g ⊗ id_T)` for every `R`-module `T`;
2. for each `i` there is a `j ≥ i` such that `f i j` dominates `f i`, that is
   `Ker(f i ⊗ id_T) ⊆ Ker(f i j ⊗ id_T)` for every `R`-module `T`;
3. for each `i` there is a `j ≥ i` such that `f i j` factors through `f i k` for every `k ≥ i`;
4. `F` is a Mittag-Leffler system: the inverse system `(Hom_R(M i, T), Hom_R(f i j, T))` is
   Mittag-Leffler for every `R`-module `T`;
5. that inverse system is Mittag-Leffler for the single module `T = ∏_{s ∈ J} M s`. -/
@[stacks 059E "Domination is spelled out as containment of the kernels of the tensored maps;
condition (4) is 059A's `IsMittagLefflerSystem`."]
public theorem tfae_isMittagLefflerSystem {R : Type u} [CommRing R] [Small.{w} R] {J : Type w}
    [Preorder J] [IsDirectedOrder J] [Nonempty J] (F : J ⥤ ModuleCat.{w} R)
    [∀ i, Module.FinitePresentation R (F.obj i)] {c : Cocone F} (hc : IsColimit c) :
    List.TFAE
      [∀ (P : ModuleCat.{w} R) [Module.FinitePresentation R P] (f : P ⟶ c.pt),
          ∃ (Q : ModuleCat.{w} R) (_ : Module.FinitePresentation R Q) (g : P ⟶ Q),
            ∀ T : ModuleCat.{w} R,
              LinearMap.ker (f.hom.rTensor T) = LinearMap.ker (g.hom.rTensor T),
        ∀ i : J, ∃ (j : J) (u : i ⟶ j), ∀ T : ModuleCat.{w} R,
          LinearMap.ker ((c.ι.app i).hom.rTensor T) ≤ LinearMap.ker ((F.map u).hom.rTensor T),
        ∀ i : J, ∃ (j : J) (u : i ⟶ j), ∀ (k : J) (v : i ⟶ k),
          ∃ h : F.obj k ⟶ F.obj j, F.map u = F.map v ≫ h,
        F.IsMittagLefflerSystem,
        (F.op ⋙ yoneda.obj (ModuleCat.of R (∀ s : J, F.obj s))).IsMittagLeffler] :=
    by exact Stacks.MittagLeffler.SystemCriterion.solution F hc

end CategoryTheory.Functor

end

/-!
# Testing the Mittag-Leffler condition on finite free modules

Let `R` be a commutative ring and `M` an `R`-module. Following 059B, a map `g : P → Q` *dominates*
a map `f : P → M` when `Ker(f ⊗ id_N) ⊆ Ker(g ⊗ id_N)` for every `R`-module `N`, and `M` is
*Mittag-Leffler* (Definition 059F) in the intrinsic form 059E (1) when every map `f : P → M` from a
finitely presented module dominates and is dominated by some map `g : P → Q` with `Q` finitely
presented. The condition need only be tested on the *finite free* modules `P`.

One direction is a weakening, a finite free module being finitely presented. The other is the
statement that mutual domination *descends along a surjection*: given `f : P → M` and a surjection
`π : F → P` with `F` finite free, a map `g' : F → Q` which dominates and is dominated by `f ∘ π`
descends to a map `g : P → Q` which dominates and is dominated by `f`. Indeed testing the
hypothesis on a module isomorphic to `R` gives `Ker(π) ⊆ Ker(f ∘ π) ⊆ Ker(g')`, so `g'` factors as
`g ∘ π`; and for every `N` the two kernels on `F ⊗ N` are the preimages of the two kernels on
`P ⊗ N` under the surjection `π ⊗ id_N`, so they are equal exactly when those are.

## Main results

* `Stacks.MittagLeffler.FiniteFreeTest.solution`: an `R`-module is Mittag-Leffler as soon as every
  map into it from a
  finite free module dominates and is dominated by a map into a finitely presented module.

## Implementation notes

Mutual domination is named `Equidominant`, as the condition 059E (1) quantifies over it, and the
mathematics of the lemma is that it descends along a surjection; the two halves of that descent are
the factorization of `g'` through `π` and the cancellation of `π ⊗ id_N` from a comparison of
kernels, the latter being an equivalence and used as such.

The finite free module surjecting onto a finitely presented `P : Type v` must itself live in
`Type v`, where the quantifiers of condition (1) sit, whereas `Fin n → R` lands in
`Type (max u v)`. It is `Shrink`, available because `R` is `v`-small, that moves it back, exactly
as in 05CN and 05CQ.

Testing the hypothesis on the single module `Shrink.{v} R` is what recovers the containment of the
untensored kernels used for the descent; the source phrases this as "the kernel of `F → Q` contains
the kernel of `F → P`", which is the case `N = R` of the assumed equality of kernels.

## References

* [StacksProject 05CP](https://stacks.math.columbia.edu/tag/05CP)
* [StacksProject 059E](https://stacks.math.columbia.edu/tag/059E)
-/

namespace Stacks.MittagLeffler.FiniteFreeTest



open scoped TensorProduct

variable {R : Type u} [CommRing R]

/-- `Equidominant f g` says that the maps `f` and `g` out of a common module dominate each other
(059B): `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every test module `N`. Condition 059E (1) asks that
every `f` out of a finitely presented module be `Equidominant` to some `g` into one. -/
private abbrev Equidominant {F M Q : Type v} [AddCommGroup F] [Module R F] [AddCommGroup M]
    [Module R M] [AddCommGroup Q] [Module R Q] (f : F →ₗ[R] M) (g : F →ₗ[R] Q) : Prop :=
  ∀ (N : Type v) [AddCommGroup N] [Module R N],
    LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)

/-- Testing domination on a module isomorphic to `R` recovers containment of the plain kernels:
this is the case `N = R` of the assumed containment of the tensored kernels. -/
private theorem ker_le_of_ker_rTensor_le {X Y Z : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] {p : X →ₗ[R] Y} {q : X →ₗ[R] Z}
    (S : Type*) [AddCommGroup S] [Module R S] (eS : S ≃ₗ[R] R)
    (h : LinearMap.ker (p.rTensor S) ≤ LinearMap.ker (q.rTensor S)) :
    LinearMap.ker p ≤ LinearMap.ker q := by
  intro x hx
  have h1 : x ⊗ₜ[R] eS.symm 1 ∈ LinearMap.ker (p.rTensor S) := by
    simp [LinearMap.mem_ker.mp hx]
  simpa using congrArg ((LinearEquiv.lTensor Z eS).trans (TensorProduct.rid R Z))
    (LinearMap.mem_ker.mp (h h1))

/-- A surjection `π` cancels from a comparison of kernels after tensoring: the kernels of
`(f ∘ π) ⊗ id_N` and `(g ∘ π) ⊗ id_N` are the preimages of the kernels of `f ⊗ id_N` and
`g ⊗ id_N` under the surjection `π ⊗ id_N`, hence are equal exactly when those are. -/
private theorem ker_rTensor_comp_eq_iff_of_surjective {X P Y Z : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup P] [Module R P] [AddCommGroup Y] [Module R Y] [AddCommGroup Z]
    [Module R Z] {π : X →ₗ[R] P} (hπ : Function.Surjective π) (p : P →ₗ[R] Y) (q : P →ₗ[R] Z)
    (N : Type*) [AddCommGroup N] [Module R N] :
    LinearMap.ker ((p ∘ₗ π).rTensor N) = LinearMap.ker ((q ∘ₗ π).rTensor N) ↔
      LinearMap.ker (p.rTensor N) = LinearMap.ker (q.rTensor N) := by
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp, LinearMap.ker_comp, LinearMap.ker_comp]
  exact (Submodule.comap_injective_of_surjective (LinearMap.rTensor_surjective N hπ)).eq_iff


/-- **Mutual domination descends along a surjection**, and this is the whole content of 05CP: if
`π : F → P` is surjective and `g' : F → Q` dominates and is dominated by `f ∘ π`, then `g'` is
`g ∘ π` for a map `g : P → Q` which dominates and is dominated by `f`. The factorization comes from
`Ker(π) ⊆ Ker(f ∘ π) ⊆ Ker(g')`, the second containment being the hypothesis tested on
`Shrink.{v} R`, and the mutual domination of `f` and `g` from cancelling the surjection
`π ⊗ id_N`. -/
private theorem exists_equidominant_of_surjective [Small.{v} R] {F P M Q : Type v} [AddCommGroup F]
    [Module R F] [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] [AddCommGroup Q]
    [Module R Q] {π : F →ₗ[R] P} (hπ : Function.Surjective π) {f : P →ₗ[R] M} {g' : F →ₗ[R] Q}
    (hg' : Equidominant (f ∘ₗ π) g') : ∃ g : P →ₗ[R] Q, Equidominant f g := by
  obtain ⟨g, hg⟩ := LinearMap.exists_comp_eq_of_ker_le hπ <|
    (LinearMap.ker_le_ker_comp π f).trans <|
    ker_le_of_ker_rTensor_le (Shrink.{v} R) (Shrink.linearEquiv R R) (hg' (Shrink.{v} R)).le
  exact ⟨g, fun N _ _ => (ker_rTensor_comp_eq_iff_of_surjective hπ f g N).mp (hg ▸ hg' N)⟩

/-- **Stacks 05CP.** Let `R` be a ring and `M` an `R`-module. Then `M` is Mittag-Leffler if and
only if for every finite free `R`-module `F` and every module map `f : F → M` there are a finitely
presented `R`-module `Q` and a module map `g : F → Q` such that `f` and `g` dominate each other,
that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. -/
public theorem solution {R : Type u} [CommRing R] [Small.{v} R]
    {M : Type v} [AddCommGroup M] [Module R M] :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (F : Type v) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
        (f : F →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : F →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  refine ⟨fun h F _ _ _ _ f => ?_, fun h P _ _ _ f => ?_⟩
  · -- A finite free module is finitely presented, so this direction is a weakening.
    have : Module.FinitePresentation R F := Module.finitePresentation_of_projective R F
    exact h F f
  · -- Apply the hypothesis to `f ∘ π` for a surjection `π` onto `P` from a finite free module in
    -- `Type v`, and descend the resulting mutual domination along `π`.
    obtain ⟨n, F, _, _, bF, π, hπ⟩ :=
      Stacks.MittagLeffler.TensorProductStable.exists_finite_free_surjective (R := R) P
    have := Module.Free.of_basis bF
    have := Module.Finite.of_basis bF
    obtain ⟨Q, _, _, _, g', hg'⟩ := h F (f ∘ₗ π)
    obtain ⟨g, hg⟩ := exists_equidominant_of_surjective hπ hg'
    exact ⟨Q, inferInstance, inferInstance, inferInstance, g, hg⟩

end Stacks.MittagLeffler.FiniteFreeTest

/-!
# Testing the Mittag-Leffler condition on finite free modules

An `R`-module `M` is *Mittag-Leffler* (Definition 059F) if the equivalent conditions of
Proposition 059E hold; only condition (1) is intrinsic to `M`, and it is the one used here: for
every finitely presented `R`-module `P` and every module map `f : P → M` there are a finitely
presented `R`-module `Q` and a module map `g : P → Q` such that `f` and `g` dominate each other,
that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N` (Definition 059B).

The condition need only be tested on the *finite free* modules `P`. One direction is a weakening,
a finite free module being finitely presented. For the other, given `f : P → M` with `P` finitely
presented, choose a surjection `p : F → P` with `F` finite free; the hypothesis produces a
finitely presented `Q` and a map `F → Q` which dominates and is dominated by `f ∘ p`. As
`Ker(F → Q) ⊇ Ker(f ∘ p) ⊇ Ker(p)`, the map `F → Q` descends to a map `g : P → Q` along `p`, and
since `p ⊗ id_N` is surjective the equality of the kernels of `(f ∘ p) ⊗ id_N` and
`(F → Q) ⊗ id_N` on `F ⊗ N` descends to the equality of the kernels of `f ⊗ id_N` and `g ⊗ id_N`
on `P ⊗ N`. So `f` and `g` dominate each other, which is condition (1) for `f`.

## Main results

* `Module.mittagLeffler_iff_forall_finite_free`: an `R`-module is Mittag-Leffler as soon as every
  map into it from a finite free module dominates and is dominated by a map into a finitely
  presented module.

## Implementation notes

The condition is spelled out inline on both sides of the equivalence, in the intrinsic form
059E (1), exactly as in 05CN and 05CQ; Mathlib's `CategoryTheory.Functor.IsMittagLeffler` is the
Mittag-Leffler condition on an inverse *system*, not on a module. Mutual domination is
spelled out as equality of the kernels of the tensored maps, `f ⊗ id_N` being `f.rTensor N`, as in
059D (`LinearMap.forall_ker_rTensor_le_iff_exists_eq_comp`).

"Finite free `R`-module" is `Module.Free R F` together with `Module.Finite R F` rather than a
chosen model `Fin n → R`: the two sides of the equivalence are the same formula, differing only in
the class of source modules quantified over, which makes the weakening direction visible as such,
and the abstract form leaves nothing for a user to transport. Nothing is lost, every finite free
module being isomorphic to some `Fin n → R` and the formula being invariant under precomposition
of `f` with an isomorphism.

The modules `M`, `P`, `F`, `Q`, `N` live in one universe `Type v` and `R` is `v`-small, as in
059D, 05CN and 05CQ. For a `v`-small `R` every finitely presented module — in particular every
finite free module — is isomorphic to one in `Type v`, and domination may be tested on finitely
presented modules alone (Lemma 059C), so the displayed quantifiers are the source's quantifiers
over all finitely presented modules, all finite free modules and all test modules.

Faithfulness. (1) No hypothesis is dead: the two displayed conditions are the two sides of the
source's equivalence, and `Small.{v} R` is what makes the quantifiers over `Type v` the source's
quantifiers over all modules; there is no hypothesis on `M` beyond being an `R`-module, as in the
source. (2) The scalars and the base are the source's: one commutative ring `R` throughout, all
maps are `R`-linear, all tensor products are `⊗[R]`, and nothing is localized or base changed.
(3) The source names no canonical map — `Q` and `g` are existentially quantified in 059E (1)
itself — and what is canonical is pinned: the maps whose kernels are compared are `f.rTensor N`
and `g.rTensor N`, not arbitrary maps `P ⊗ N → M ⊗ N` and `P ⊗ N → Q ⊗ N`. (4) The instantiation
is not degenerate, and neither side is vacuous or automatic: both hold whenever `M` is finitely
presented, with `Q = M` and `g = f`, and both fail for `R = ℤ` and `M = ℚ`, which is flat and
countably generated but not projective (Theorem 059Z) — the right-hand one already at `F = ℤ` and
`f : 1 ↦ 1`, since `Ker(f ⊗ id_{ℤ/m}) = ℤ/m` for every `m` forces `g 1 ∈ ⋂_m m · Q = 0`, whence
`g = 0` and `Ker(g ⊗ id_ℤ) = ℤ ≠ 0 = Ker(f ⊗ id_ℤ)`. The right-hand condition is a genuine
restriction of the left-hand one, the finitely presented modules not all being free.

## References

* [StacksProject 05CP](https://stacks.math.columbia.edu/tag/05CP)
-/



@[expose] public section

/-- **Stacks 05CP.** Let `R` be a ring and `M` an `R`-module. Then `M` is Mittag-Leffler if and
only if for every finite free `R`-module `F` and every module map `f : F → M` there are a finitely
presented `R`-module `Q` and a module map `g : F → Q` such that `f` and `g` dominate each other,
that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. Being Mittag-Leffler is spelled
out in the intrinsic form 059E (1): the same condition with `F` ranging over all finitely
presented modules. -/
@[stacks 05CP "Mittag-Leffler is spelled out inline as condition (1) of 059E; domination as
equality of the kernels of the tensored maps."]
public theorem Module.mittagLeffler_iff_forall_finite_free {R : Type u} [CommRing R] [Small.{v} R]
    {M : Type v} [AddCommGroup M] [Module R M] :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (F : Type v) [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
        (f : F →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : F →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) :=
    by apply Stacks.MittagLeffler.FiniteFreeTest.solution

/-! ### A presenting system of finitely presented modules

Every module is the colimit of a directed system of finitely presented modules: index the system
by a finite subset `T` of `M` together with a finite set of candidate relations, take `R^T` modulo
those of the candidates that lie in `R^T` and are killed by the canonical surjection, and map the
result to `M`. The construction is shared by the flat-descent and the
flat-plus-countably-generated-implies-projective arguments. -/

namespace Stacks.MittagLeffler.PresentingSystem

section System

variable (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The canonical surjection onto `M` from the free `R`-module on the underlying set of `M`, with
scalars transported into the universe of `M`. -/
public noncomputable def freeProj : (M →₀ Shrink.{v} R) →ₗ[R] M :=
  Finsupp.lsum R fun x ↦ LinearMap.toSpanSingleton R M x ∘ₗ (Shrink.linearEquiv R R).toLinearMap

/-- The surjection `freeProj` on a generator: a single basis element maps to its own scalar
multiple. -/
public theorem freeProj_single (x : M) (r : Shrink.{v} R) :
    freeProj R M (Finsupp.single x r) = Shrink.linearEquiv R R r • x := by
  simp [freeProj, LinearMap.toSpanSingleton_apply]

/-- The free direct summand of `M →₀ Shrink R` supported on a finite subset `T` of `M`. -/
public noncomputable abbrev freePart (T : Finset M) : Submodule R (M →₀ Shrink.{v} R) :=
  Finsupp.supported (Shrink.{v} R) R (↑T : Set M)

/-- The index set of the presenting system of `M`: a finite subset `T` of `M`, giving the free
part `R^T`, together with a finite set of elements of `M →₀ Shrink R` whose members lying in
`R^T ∩ Ker p` are the relations imposed. -/
public abbrev Idx : Type v := Finset M × Finset (M →₀ Shrink.{v} R)

/-- The submodule of relations at an index: the span of those members of the chosen finite set
which lie in the free part and are killed by `freeProj`. -/
public noncomputable abbrev rels (i : Idx R M) : Submodule R (freePart R M i.1) :=
  Submodule.span R
    {y | (y : M →₀ Shrink.{v} R) ∈ i.2 ∧ freeProj R M (y : M →₀ Shrink.{v} R) = 0}

/-- The members of the presenting system: `R^T` modulo the finitely many chosen relations. -/
public noncomputable abbrev sys (i : Idx R M) : Type v := (freePart R M i.1) ⧸ rels R M i

/-- Enlarging the index carries the relations into the relations. -/
public theorem rels_le {i j : Idx R M} (h : i ≤ j) :
    rels R M i ≤ (rels R M j).comap
      (Submodule.inclusion (Finsupp.supported_mono (Finset.coe_subset.2 h.1))) := by
  refine Submodule.span_le.2 ?_
  rintro y ⟨hy1, hy2⟩
  exact Submodule.subset_span ⟨h.2 hy1, hy2⟩

/-- The transition maps of the presenting system. -/
public noncomputable def trans (i j : Idx R M) (h : i ≤ j) : sys R M i →ₗ[R] sys R M j :=
  Submodule.mapQ _ _ (Submodule.inclusion (Finsupp.supported_mono (Finset.coe_subset.2 h.1)))
    (rels_le R M h)

/-- The transition map on a class: it is induced by the inclusion of the free parts. -/
public theorem trans_mk (i j : Idx R M) (h : i ≤ j) (y : freePart R M i.1) :
    trans R M i j h (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (Submodule.inclusion
        (Finsupp.supported_mono (Finset.coe_subset.2 h.1)) y) := rfl

/-- The canonical maps from the members of the presenting system to `M`. -/
public noncomputable def toM (i : Idx R M) : sys R M i →ₗ[R] M :=
  Submodule.liftQ _ (freeProj R M ∘ₗ (freePart R M i.1).subtype) (by
    refine Submodule.span_le.2 ?_
    rintro y ⟨-, hy⟩
    simpa using hy)

/-- The map to `M` on a class: it is `freeProj` on a representative. -/
public theorem toM_mk (i : Idx R M) (y : freePart R M i.1) :
    toM R M i (Submodule.Quotient.mk y) = freeProj R M (y : M →₀ Shrink.{v} R) := rfl

/-- The maps to `M` are compatible with the transition maps. -/
public theorem toM_trans (i j : Idx R M) (h : i ≤ j) (x : sys R M i) :
    toM R M j (trans R M i j h x) = toM R M i x := by
  obtain ⟨y, rfl⟩ := (rels R M i).mkQ_surjective x
  rfl

omit [AddCommGroup M] [Module R M] in
/-- The free part at a finite subset is finitely presented. -/
public theorem finitePresentation_freePart (T : Finset M) :
    Module.FinitePresentation R (freePart R M T) := by
  have hfin : Module.Finite R ((↑T : Set M) →₀ Shrink.{v} R) :=
    Module.Finite.equiv (Finsupp.linearEquivFunOnFinite R (Shrink.{v} R) (↑T : Set M)).symm
  have : Module.FinitePresentation R ((↑T : Set M) →₀ Shrink.{v} R) :=
    Module.finitePresentation_of_projective _ _
  exact Module.FinitePresentation.of_equiv (Finsupp.supportedEquivFinsupp _).symm

end System

end Stacks.MittagLeffler.PresentingSystem

end
