module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Right exact linear endofunctors of modules are tensor products

The proof of [Stacks, Tag 0EX3] (b) runs the functor
`M ↦ H^d(X', F' ⊗_{O_{X'}} (f')^* M~)` on `R'`-modules through the assertion that

> any right exact `R'`-linear functor `Mod_{R'} ⥤ Mod_{R'}` which commutes with direct sums
> is given by tensoring with an `R'`-module

which the source states and then leaves to the reader. This file proves it. It is the algebraic
core of top-degree base change, and it is pure module theory: no scheme, no sheaf and no
cohomology occurs below.

## Main definitions

* `Stacks.EilenbergWatts.map`: the comparison `F(R) ⊗[R] M →ₗ[R] F(M)`, sending `x ⊗ m` to
  `F(r ↦ r • m)` applied to `x`.
* `Stacks.EilenbergWatts.trans`: the same maps assembled into a natural transformation
  `tensorLeft (F.obj (ModuleCat.of R R)) ⟶ F`.
* `Stacks.EilenbergWatts.iso`: that natural transformation, as a natural isomorphism.
* `Stacks.ModuleCat.finsuppCofan`: the free module `ι →₀ R` as the coproduct of copies of `R`.

## Main results

* `Stacks.EilenbergWatts.isIso_trans`: for an additive `R`-linear endofunctor of `ModuleCat R`
  which preserves finite colimits and arbitrary coproducts, the comparison is an isomorphism.
* `Stacks.EilenbergWatts.linearEquiv`: the comparison as an `R`-linear equivalence
  `F(R) ⊗[R] M ≃ₗ[R] F(M)`.
* `Stacks.EilenbergWatts.isIso_of_isIso_app_self` and
  `Stacks.EilenbergWatts.isIso_app_of_isIso_app_self`: **Eilenberg-Watts rigidity.** A natural
  transformation between two right exact additive endofunctors of `ModuleCat R` which commute
  with arbitrary direct sums is an isomorphism as soon as it is an isomorphism at the base ring.
  The invertibility half of the theorem above uses nothing else about the comparison, so it is
  proved in this generality and the comparison is the case it is applied to; a concretely given
  comparison is then identified with the abstract one by no uniqueness theorem at all.
* `CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan`: a natural transformation that is an
  isomorphism on a family of objects, between two functors preserving that family's coproduct,
  is an isomorphism on the coproduct.

## Implementation notes

"Right exact" is `CategoryTheory.Limits.PreservesFiniteColimits`: for an additive functor between
abelian categories that is equivalent to preserving cokernels
(`CategoryTheory.Functor.preservesFiniteColimits_tfae`), which is the source's hypothesis.
"Commutes with direct sums" is `PreservesColimitsOfShape (Discrete ι)` for every index type `ι`
in the module universe; only two index types are used, the carriers of `M` and of a kernel
submodule of a free module on it.

`R`-linearity of `F` enters exactly once, in `Stacks.EilenbergWatts.bil`: it is what makes
`x ↦ F(r ↦ r • m)(x)` balanced over `R`, hence what lets the comparison factor through the tensor
product. Additivity alone would only give a map out of `F(R) ⊗[ℤ] M`.

The proof is the source's: the comparison is the right unitor at `M = R`, hence an isomorphism
there; coproduct preservation on both sides propagates that to free modules; and the tautological
presentation of an arbitrary `M` by free modules, together with right exactness on both sides,
propagates it to `M` by a two-step element chase (surjectivity needs only the right-hand square,
injectivity needs the exactness of the images of the presentation).

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct

namespace CategoryTheory.NatTrans

variable {C : Type*} [Category C] {D : Type*} [Category D] {G H : C ⥤ D}

/-- A natural transformation which is an isomorphism on each member of a family of objects is an
isomorphism on the coproduct of the family, provided both functors take the coproduct cofan to a
colimit cofan. -/
lemma isIso_app_of_isColimit_cofan (τ : G ⟶ H) {ι : Type*} {f : ι → C} (c : Cofan f)
    (hG : IsColimit (G.mapCocone c)) (hH : IsColimit (H.mapCocone c))
    (h : ∀ i, IsIso (τ.app (f i))) : IsIso (τ.app c.pt) := by
  let d : Cocone ((Discrete.functor f) ⋙ H) :=
    { pt := G.obj c.pt
      ι := Discrete.natTrans (fun i => inv (τ.app (f i.as)) ≫ G.map (c.inj i.as)) }
  have hd : ∀ j : ι, d.ι.app ⟨j⟩ = inv (τ.app (f j)) ≫ G.map (c.ι.app ⟨j⟩) := fun _ => rfl
  have key : ∀ j : ι, G.map (c.ι.app ⟨j⟩) ≫ τ.app c.pt = τ.app (f j) ≫ H.map (c.ι.app ⟨j⟩) :=
    fun j => τ.naturality _
  have hfac : ∀ j : ι, H.map (c.ι.app ⟨j⟩) ≫ hH.desc d = d.ι.app ⟨j⟩ := fun j => by
    simpa only [Functor.mapCocone_ι_app] using hH.fac d ⟨j⟩
  refine ⟨hH.desc d, ?_, ?_⟩
  · refine hG.hom_ext (fun ⟨j⟩ => ?_)
    simp only [Functor.mapCocone_ι_app]
    rw [reassoc_of% key j, hfac j, hd j, IsIso.hom_inv_id_assoc]
    simp
  · refine hH.hom_ext (fun ⟨j⟩ => ?_)
    simp only [Functor.mapCocone_ι_app]
    rw [← Category.assoc, hfac j, hd j, Category.assoc, key j, IsIso.inv_hom_id_assoc]
    simp

end CategoryTheory.NatTrans

namespace Stacks

variable {R : Type u} [CommRing R]

namespace ModuleCat

/-- The free module `ι →₀ R`, presented as a coproduct of copies of `R` indexed by `ι`. -/
noncomputable def finsuppCofan (ι : Type u) :
    Cofan (fun _ : ι => ModuleCat.of R R) :=
  Cofan.mk (ModuleCat.of R (ι →₀ R)) (fun i => ModuleCat.ofHom (Finsupp.lsingle i))

/-- The cone point of `finsuppCofan ι` is the free module `ι →₀ R`. -/
@[simp]
lemma finsuppCofan_pt (ι : Type u) :
    (finsuppCofan (R := R) ι).pt = ModuleCat.of R (ι →₀ R) :=
  rfl

/-- The free module `ι →₀ R` is the coproduct of copies of `R` indexed by `ι`. -/
noncomputable def isColimitFinsuppCofan (ι : Type u) : IsColimit (finsuppCofan (R := R) ι) :=
  Cofan.IsColimit.mk _ (fun t => ModuleCat.ofHom (Finsupp.lsum R (fun i => (t.inj i).hom)))
    (by intro t j; ext; simp [finsuppCofan])
    (by
      intro t m hm
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext'
      intro i
      have h : m.hom ∘ₗ (Finsupp.lsingle i : R →ₗ[R] (ι →₀ R)) = (t.inj i).hom := by
        rw [← hm i]; rfl
      refine h.trans ?_
      apply LinearMap.ext
      intro r
      change (t.inj i).hom r = Finsupp.lsum R (fun j => (t.inj j).hom) (Finsupp.single i r)
      simp)

/-- The tautological presentation of a module by the free module on its own carrier:
`Finsupp.single m r ↦ r • m`. -/
noncomputable def freeCover (M : ModuleCat.{u} R) : ModuleCat.of R (↥M →₀ R) ⟶ M :=
  ModuleCat.ofHom (Finsupp.lsum R (fun m => LinearMap.toSpanSingleton R M m))

/-- `freeCover M` sends `Finsupp.single m r` to `r • m`. -/
@[simp]
lemma freeCover_single (M : ModuleCat.{u} R) (m : M) (r : R) :
    (freeCover M).hom (Finsupp.single m r) = r • m := by
  simp [freeCover, LinearMap.toSpanSingleton]

/-- The tautological presentation `freeCover M` is surjective. -/
lemma freeCover_surjective (M : ModuleCat.{u} R) : Function.Surjective (freeCover M).hom :=
  fun m => ⟨Finsupp.single m 1, by rw [freeCover_single, one_smul]⟩

/-- `freeCover M` sends `Finsupp.single m 1` to `m`. -/
lemma freeCover_single_one (M : ModuleCat.{u} R) (m : M) :
    (freeCover M).hom (Finsupp.single m 1) = m := by
  rw [freeCover_single, one_smul]

/-- The tautological presentation `freeCover M` is an epimorphism. -/
instance (M : ModuleCat.{u} R) : Epi (freeCover M) :=
  (ModuleCat.epi_iff_surjective _).2 (freeCover_surjective M)

end ModuleCat

namespace EilenbergWatts

/-- A right exact additive functor carries an exact `B ⟶ A ⟶ M` with `A ⟶ M` epi to an exact
sequence with epi right-hand map. This is
`CategoryTheory.Functor.preservesFiniteColimits_tfae`, read off at the second of its four
equivalent conditions. -/
lemma exact_map_and_epi (G : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [G.Additive]
    [PreservesFiniteColimits G] (S : ShortComplex (ModuleCat.{u} R)) (h : S.Exact)
    (he : Epi S.g) : (S.map G).Exact ∧ Epi (G.map S.g) :=
  (show ∀ T : ShortComplex (ModuleCat.{u} R), T.Exact ∧ Epi T.g →
      (T.map G).Exact ∧ Epi (G.map T.g) from
    ((Functor.preservesFiniteColimits_tfae G).out 4 2).mp
      (inferInstance : PreservesFiniteColimits G)) S ⟨h, he⟩

/-! ### The rigidity criterion

The invertibility half of the theorem below uses nothing about the Eilenberg-Watts comparison
except that it is a natural transformation between two right exact additive endofunctors of
`ModuleCat R` which commute with arbitrary direct sums.  It is therefore stated for an arbitrary
such transformation: *a natural transformation between two such functors which is an isomorphism
at the base ring is an isomorphism*.  That is what identifies a concretely given comparison with
the abstract one without any uniqueness theorem, and it is what conclusion (b) of
[Stacks, Tag 0EX3] consumes.
-/

section Criterion

variable {G H : ModuleCat.{u} R ⥤ ModuleCat.{u} R} [G.Additive] [H.Additive]

/-- **A natural transformation between two right exact functors is an isomorphism at `M` as soon
as it is at the two terms of a presentation `B ⟶ A ⟶ M ⟶ 0` of `M`.**  Both functors are right
exact, so the images of the presentation under them are again exact with epi right-hand map, and
the conclusion is the resulting element chase: surjectivity needs only the right-hand square,
injectivity needs the exactness of the images of the presentation. -/
lemma isIso_app_of_presentation [PreservesFiniteColimits G] [PreservesFiniteColimits H]
    (τ : G ⟶ H) {B A M : ModuleCat.{u} R} (u : B ⟶ A) (π : A ⟶ M)
    (hrange : LinearMap.range u.hom = LinearMap.ker π.hom) [Epi π]
    (hB : IsIso (τ.app B)) (hA : IsIso (τ.app A)) :
    IsIso (τ.app M) := by
  have hS := ShortComplex.Exact.moduleCat_of_range_eq_ker u π hrange
  obtain ⟨hHex, hHepi⟩ := exact_map_and_epi H _ hS ‹Epi π›
  obtain ⟨hGex, hGepi⟩ := exact_map_and_epi G _ hS ‹Epi π›
  rw [ShortComplex.moduleCat_exact_iff] at hHex hGex
  simp only [ShortComplex.map_X₂, ShortComplex.map_f, ShortComplex.map_g,
    ShortComplex.moduleCatMkOfKerLERange_f, ShortComplex.moduleCatMkOfKerLERange_g] at hHex hGex
  have hHsurj : Function.Surjective (H.map π).hom := (ModuleCat.epi_iff_surjective _).1 hHepi
  have hGsurj : Function.Surjective (G.map π).hom := (ModuleCat.epi_iff_surjective _).1 hGepi
  have hnat : ∀ {Z W : ModuleCat.{u} R} (g : Z ⟶ W) (z : G.obj Z),
      (τ.app W).hom ((G.map g).hom z) = (H.map g).hom ((τ.app Z).hom z) := fun g z =>
    congrArg (fun h : G.obj _ ⟶ H.obj _ => h.hom z) (τ.naturality g)
  have hBbij := (ConcreteCategory.isIso_iff_bijective (τ.app B)).1 hB
  have hAbij := (ConcreteCategory.isIso_iff_bijective (τ.app A)).1 hA
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun z z' hz => ?_, fun y => ?_⟩
  · rw [← sub_eq_zero] at hz ⊢
    rw [← map_sub] at hz
    obtain ⟨w, hw⟩ := hGsurj (z - z')
    rw [← hw, hnat π w] at hz
    obtain ⟨b, hb⟩ := hHex _ hz
    obtain ⟨b', rfl⟩ := hBbij.2 b
    have hb' : (τ.app A).hom ((G.map u).hom b') = (τ.app A).hom w := by
      rw [hnat u b']; exact hb
    rw [← hw, ← hAbij.1 hb', ← ModuleCat.comp_apply, ← G.map_comp,
      show u ≫ π = 0 from (ShortComplex.moduleCatMkOfKerLERange u π hrange.le).zero]
    simp
  · obtain ⟨a, rfl⟩ := hHsurj y
    obtain ⟨a', rfl⟩ := hAbij.2 a
    exact ⟨(G.map π).hom a', hnat π a'⟩

variable [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) G]
  [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) H]

omit [G.Additive] [H.Additive] in
/-- **A natural transformation which is an isomorphism at the base ring is an isomorphism at
every free module**: both functors preserve the coproduct decomposition of `ι →₀ R` into copies
of `R`. -/
lemma isIso_app_finsupp (τ : G ⟶ H) (h : IsIso (τ.app (ModuleCat.of R R))) (ι : Type u) :
    IsIso (τ.app (ModuleCat.of R (ι →₀ R))) :=
  CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan τ (Stacks.ModuleCat.finsuppCofan ι)
    (isColimitOfPreserves _ (Stacks.ModuleCat.isColimitFinsuppCofan ι))
    (isColimitOfPreserves _ (Stacks.ModuleCat.isColimitFinsuppCofan ι)) (fun _ => h)

variable [PreservesFiniteColimits G] [PreservesFiniteColimits H]

/-- **Eilenberg-Watts rigidity, at a module.**  A natural transformation between two right exact
additive endofunctors of `ModuleCat R` which commute with arbitrary direct sums, and which is an
isomorphism at the base ring, is an isomorphism at every module: coproduct preservation
propagates the hypothesis to free modules, and the tautological presentation of a module by free
modules propagates it from there. -/
lemma isIso_app_of_isIso_app_self (τ : G ⟶ H) (h : IsIso (τ.app (ModuleCat.of R R)))
    (M : ModuleCat.{u} R) : IsIso (τ.app M) := by
  set π := Stacks.ModuleCat.freeCover M with hπ
  set K := LinearMap.ker π.hom with hK
  refine isIso_app_of_presentation τ
    (Stacks.ModuleCat.freeCover (ModuleCat.of R ↥K) ≫ ModuleCat.ofHom K.subtype) π ?_
    (isIso_app_finsupp τ h _) (isIso_app_finsupp τ h _)
  apply le_antisymm
  · rintro x ⟨b, rfl⟩
    exact ((Stacks.ModuleCat.freeCover (ModuleCat.of R ↥K)).hom b).2
  · intro x hx
    refine ⟨Finsupp.single ⟨x, hx⟩ 1, ?_⟩
    change K.subtype ((Stacks.ModuleCat.freeCover (ModuleCat.of R ↥K)).hom
      (Finsupp.single ⟨x, hx⟩ 1)) = x
    rw [Stacks.ModuleCat.freeCover_single_one]
    rfl

/-- **Eilenberg-Watts rigidity.**  A natural transformation between two right exact additive
endofunctors of `ModuleCat R` which commute with arbitrary direct sums is an isomorphism as soon
as it is an isomorphism at the base ring. -/
lemma isIso_of_isIso_app_self (τ : G ⟶ H) (h : IsIso (τ.app (ModuleCat.of R R))) : IsIso τ :=
  have := fun M => isIso_app_of_isIso_app_self τ h M
  NatIso.isIso_of_isIso_app τ

end Criterion

/-- **Eilenberg-Watts rigidity, through a pair of natural isomorphisms.**  The two functors a
concretely given comparison is a transformation between are rarely the two that right exactness
and coproduct preservation have been proved for; this is the criterion with that discrepancy
taken as data.  A natural transformation `τ : G ⟶ H` which is an isomorphism at the base ring is
an isomorphism at every module as soon as `G` and `H` are naturally isomorphic to two functors
which are right exact additive and commute with arbitrary direct sums. -/
lemma isIso_app_of_isIso_app_self_of_natIso
    {G H G' H' : ModuleCat.{u} R ⥤ ModuleCat.{u} R} [G'.Additive] [H'.Additive]
    [PreservesFiniteColimits G'] [PreservesFiniteColimits H']
    [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) G']
    [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) H']
    (u : G' ≅ G) (v : H ≅ H') (τ : G ⟶ H)
    (h : IsIso (τ.app (ModuleCat.of R R))) (M : ModuleCat.{u} R) :
    IsIso (τ.app M) := by
  have hM : IsIso (u.hom.app M ≫ τ.app M ≫ v.hom.app M) :=
    isIso_app_of_isIso_app_self (u.hom ≫ τ ≫ v.hom)
      (by simp only [NatTrans.comp_app]; infer_instance) M
  have := IsIso.of_isIso_comp_left (u.hom.app M) (τ.app M ≫ v.hom.app M)
  exact IsIso.of_isIso_comp_right (τ.app M) (v.hom.app M)

variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] [Functor.Linear R F]

/-- `F` applied to the multiplication map `r ↦ r • m`, as an `R`-bilinear map in `m` and in the
argument. `R`-linearity of `F` is what makes this `R`-linear in `m`. -/
noncomputable def bil (M : ModuleCat.{u} R) :
    M →ₗ[R] (F.obj (ModuleCat.of R R) →ₗ[R] F.obj M) where
  toFun m := (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom
  map_add' m m' := by
    have h : (LinearMap.toSpanSingleton R M (m + m')) =
        LinearMap.toSpanSingleton R M m + LinearMap.toSpanSingleton R M m' := by
      ext; simp [LinearMap.toSpanSingleton, smul_add]
    rw [show ModuleCat.ofHom (LinearMap.toSpanSingleton R M (m + m')) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R M m) +
        ModuleCat.ofHom (LinearMap.toSpanSingleton R M m') by rw [h]; rfl]
    rw [F.map_add]
    rfl
  map_smul' r m := by
    have h : (LinearMap.toSpanSingleton R M (r • m)) =
        (LinearMap.toSpanSingleton R M m) ∘ₗ (r • LinearMap.id) := by
      ext; simp [LinearMap.toSpanSingleton, smul_smul, mul_comm]
    rw [show ModuleCat.ofHom (LinearMap.toSpanSingleton R M (r • m)) =
      (r • (𝟙 (ModuleCat.of R R))) ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R M m) by
        rw [h]; ext; simp [LinearMap.toSpanSingleton]]
    rw [F.map_comp, Functor.Linear.map_smul]
    ext x
    simp

/-- The Eilenberg-Watts comparison map `F(R) ⊗[R] M →ₗ[R] F(M)`. -/
noncomputable def map (M : ModuleCat.{u} R) :
    (F.obj (ModuleCat.of R R)) ⊗[R] M →ₗ[R] F.obj M :=
  TensorProduct.lift (bil F M).flip

/-- The comparison `map F M` sends `x ⊗ m` to `F(r ↦ r • m)` applied to `x`. -/
@[simp]
lemma map_tmul (M : ModuleCat.{u} R) (x : F.obj (ModuleCat.of R R)) (m : M) :
    map F M (x ⊗ₜ m) = (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom x :=
  rfl

/-- The Eilenberg-Watts comparison, as a natural transformation
`F(R) ⊗ - ⟶ F`. -/
noncomputable def trans : tensorLeft (F.obj (ModuleCat.of R R)) ⟶ F where
  app M := ModuleCat.ofHom (map F M)
  naturality M N g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro y m
    change map F N (y ⊗ₜ (g.hom m)) = (F.map g).hom (map F M (y ⊗ₜ m))
    have h : ModuleCat.ofHom (LinearMap.toSpanSingleton R N (g.hom m)) =
        ModuleCat.ofHom (LinearMap.toSpanSingleton R M m) ≫ g := by
      ext; simp [LinearMap.toSpanSingleton]
    rw [map_tmul, map_tmul, h, F.map_comp, ModuleCat.comp_apply]

/-- The component of `trans F` at `M` sends `x ⊗ m` to `F(r ↦ r • m)` applied to `x`. -/
@[simp]
lemma trans_app_tmul (M : ModuleCat.{u} R) (x : F.obj (ModuleCat.of R R)) (m : M) :
    ((trans F).app M).hom (x ⊗ₜ m) =
      (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom x :=
  rfl

/-- At `M = R` the comparison is the right unitor, hence an isomorphism. -/
instance isIso_trans_app_self : IsIso ((trans F).app (ModuleCat.of R R)) := by
  have h : ((trans F).app (ModuleCat.of R R)).hom =
      (TensorProduct.rid R (F.obj (ModuleCat.of R R))).toLinearMap := by
    apply TensorProduct.ext'
    intro x r
    change (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R R r))).hom x = _
    rw [show ModuleCat.ofHom (LinearMap.toSpanSingleton R R r) = r • 𝟙 (ModuleCat.of R R) by
      ext; simp [LinearMap.toSpanSingleton, mul_comm]]
    rw [Functor.Linear.map_smul]
    simp
  exact ⟨ModuleCat.ofHom (TensorProduct.rid R (F.obj (ModuleCat.of R R))).symm.toLinearMap,
    ModuleCat.hom_ext (by rw [ModuleCat.hom_comp, h]; ext x; simp),
    ModuleCat.hom_ext (by rw [ModuleCat.hom_comp, h]; ext x; simp)⟩

section

variable [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F]

/-- The comparison is an isomorphism at a free module: both sides preserve the coproduct
decomposition of `ι →₀ R` into copies of `R`, where the comparison is the right unitor.  This is
`isIso_app_finsupp` at the Eilenberg-Watts comparison. -/
instance isIso_trans_app_finsupp (ι : Type u) :
    IsIso ((trans F).app (ModuleCat.of R (ι →₀ R))) := by
  have : PreservesColimitsOfShape (Discrete ι) (tensorLeft (F.obj (ModuleCat.of R R))) :=
    inferInstance
  exact NatTrans.isIso_app_of_isColimit_cofan (trans F) (Stacks.ModuleCat.finsuppCofan ι)
    (isColimitOfPreserves _ (Stacks.ModuleCat.isColimitFinsuppCofan ι))
    (isColimitOfPreserves _ (Stacks.ModuleCat.isColimitFinsuppCofan ι))
    (fun _ => isIso_trans_app_self F)

variable [PreservesFiniteColimits F]

omit [∀ ι : Type u, PreservesColimitsOfShape (Discrete ι) F] in
/-- The comparison is an isomorphism at `M` as soon as it is at the two terms of a presentation
`B ⟶ A ⟶ M ⟶ 0` of `M`.  This is `isIso_app_of_presentation` at the Eilenberg-Watts
comparison. -/
lemma isIso_trans_app_of_presentation {B A M : ModuleCat.{u} R} (u : B ⟶ A) (π : A ⟶ M)
    (hrange : LinearMap.range u.hom = LinearMap.ker π.hom) [Epi π]
    (hB : IsIso ((trans F).app B)) (hA : IsIso ((trans F).app A)) :
    IsIso ((trans F).app M) :=
  isIso_app_of_presentation (trans F) u π hrange hB hA

/-- The comparison is an isomorphism at every module.  This is Eilenberg-Watts rigidity
(`isIso_app_of_isIso_app_self`) at the comparison itself, whose value at the base ring is the
right unitor. -/
instance isIso_trans_app (M : ModuleCat.{u} R) : IsIso ((trans F).app M) := by
  set π := Stacks.ModuleCat.freeCover M with hπ
  set K := LinearMap.ker π.hom with hK
  refine isIso_trans_app_of_presentation F
    (Stacks.ModuleCat.freeCover (ModuleCat.of R ↥K) ≫ ModuleCat.ofHom K.subtype) π ?_
    (isIso_trans_app_finsupp F _) (isIso_trans_app_finsupp F _)
  apply le_antisymm
  · rintro x ⟨b, rfl⟩
    exact ((Stacks.ModuleCat.freeCover (ModuleCat.of R ↥K)).hom b).2
  · intro x hx
    refine ⟨Finsupp.single ⟨x, hx⟩ 1, ?_⟩
    change K.subtype ((Stacks.ModuleCat.freeCover (ModuleCat.of R ↥K)).hom
      (Finsupp.single ⟨x, hx⟩ 1)) = x
    rw [Stacks.ModuleCat.freeCover_single_one]
    rfl

/-- The Eilenberg-Watts comparison `trans F` is a natural isomorphism. -/
instance isIso_trans : IsIso (trans F) :=
  NatIso.isIso_of_isIso_app _

/-- **Eilenberg-Watts**: a right exact `R`-linear endofunctor of `R`-modules which commutes with
arbitrary direct sums is tensoring with the module `F(R)`. -/
noncomputable def iso : tensorLeft (F.obj (ModuleCat.of R R)) ≅ F :=
  asIso (trans F)

/-- The forward map of `iso F` is the comparison `trans F`. -/
@[simp]
lemma iso_hom : (iso F).hom = trans F := rfl

/-- The Eilenberg-Watts comparison at a single module, as an `R`-linear equivalence. -/
noncomputable def linearEquiv (M : ModuleCat.{u} R) :
    (F.obj (ModuleCat.of R R)) ⊗[R] M ≃ₗ[R] F.obj M :=
  LinearEquiv.ofBijective (map F M)
    ((ConcreteCategory.isIso_iff_bijective _).1 (isIso_trans_app F M))

/-- The equivalence `linearEquiv F M` sends `x ⊗ m` to `F(r ↦ r • m)` applied to `x`. -/
@[simp]
lemma linearEquiv_tmul (M : ModuleCat.{u} R) (x : F.obj (ModuleCat.of R R)) (m : M) :
    linearEquiv F M (x ⊗ₜ m) =
      (F.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M m))).hom x :=
  rfl

end

end EilenbergWatts

end Stacks
