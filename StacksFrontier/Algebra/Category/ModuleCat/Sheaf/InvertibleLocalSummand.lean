module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Invertible modules are locally direct summands of finite free modules

Let `O` be a sheaf of commutative rings on a site and let `L` be a sheaf of `O`-modules. Stacks
Tag 0B8N part (b) asserts that if `L` is invertible then every object of the site has a covering
on whose members `L` restricts to a direct summand of a finite free module. This file supplies
the two ingredients of that statement which are not already in the library: the fact that a
universal map into a sheaf of modules is automatically locally surjective, and the splitting
produced by a dual basis for the tensor pairing.

## Main definitions

* `Stacks.SheafOfModules.imgSieve`: the sieve of arrows along which a section of a sheaf of
  modules restricts into the image of a morphism of presheaves of modules.
* `Stacks.SheafOfModules.localImage`: the submodule of a sheaf of modules consisting of the
  sections which locally lie in the image of a morphism of presheaves of modules. Its membership
  condition is local, so it is a `SheafOfModules.Submodule`.
* `Stacks.SheafOfModules.toLocalImage`: the factorization of the morphism through that submodule.
* `Stacks.SheafOfModules.coev`, `Stacks.SheafOfModules.contract` and
  `Stacks.SheafOfModules.proj`: tensoring on the right with a global section, contracting a
  pairing against a global section, and the resulting projection `L ⊗ N ⟶ L`.
* `Stacks.SheafOfModules.sliceFunctor`: restriction of presheaves of modules to the slice site
  over an object, spelled as `PresheafOfModules.pushforward₀OfCommRingCat` so that Mathlib's
  monoidal structure on it is available.

## Main results

* `Stacks.SheafOfModules.isLocallySurjective_of_universal`: a morphism of presheaves of modules
  `ψ : K ⟶ A.val` into a sheaf of modules through which every morphism to a sheaf of modules
  factors uniquely — that is, one exhibiting `A` as the sheafification of `K` — is locally
  surjective. **No sheafification instance is required.**
* `Stacks.SheafOfModules.isSplitMono_of_dualBasis`: the algebraic core of Tag 0B8N (b). A
  locally bijective pairing `ψ : L ⊗ N ⟶ O` together with finitely many global sections `x j`
  of `L` and `y j` of `N` whose pairings sum to `1` exhibits `L` as a direct summand of a finite
  free module.
* `Stacks.SheafOfModules.structureSheaf_comp_forget`, `Stacks.SheafOfModules.sliceFunctor_unit` and
  `Stacks.SheafOfModules.over_val`: the identifications of the slice-site structure sheaf, of
  the monoidal unit and of the restricted module, all definitional.

## Implementation notes

`isLocallySurjective_of_universal` is proved by a subobject argument rather than by comparison
with a sheafification functor, and this is what makes it unconditional. The sections of `A` that
locally lie in the image of `ψ` form a `SheafOfModules.Submodule` — closure under addition is
intersection of covering sieves, closure under the action of the structure sheaf is
`J.superset_covering`, stability under restriction is `J.pullback_stable`, and the locality of
the membership condition is `J.transitive`. The morphism `ψ` factors through that submodule, so
the universal property provides a section of its inclusion; the inclusion is a monomorphism, so
it is an isomorphism and the submodule is everything.

`isSplitMono_of_dualBasis` deliberately avoids any tensor product of *sheaves* of modules: the
pinned Mathlib has no `MonoidalCategory (SheafOfModules R)`, so the pairing is a morphism of
presheaves of modules and the retraction is obtained from
`PresheafOfModules.homEquivOfIsLocallyBijective`, which factors a morphism out of `L ⊗ N` into a
sheaf uniquely through a locally bijective `ψ`. The split monomorphism and its retraction are
assembled from the components with `Limits.Pi.lift` and `Limits.Pi.π`, using only that
`SheafOfModules R` is preadditive and has finite products; in particular no identification of a
finite product with `SheafOfModules.free` is needed.

The maps `coev`, `contract` and `proj` are built from the unitors and whiskerings of the
monoidal structure on presheaves of modules rather than by hand, which makes their naturality
automatic and their values on sections definitional. For the Mathlib simp set to apply, the
indexing ring presheaf must be spelled
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O`, a reducible
abbreviation for `O ⋙ forget₂ CommRingCat RingCat`; spelled as
  `(Stacks.SheafOfModules.TensorSheafification.structureSheaf O
hO).obj` the monoidal instance has to be transported by hand and no element-level lemma matches.
This is why the statements here are indexed by the ring presheaf and the sheaf of modules is
written `⟨Lp, hLp⟩`.

Universes are those of Stacks Tag 05NA: the site objects and morphisms
live in independent universes `u` and `v`, while the ring and module sections share a universe
`w`, as Mathlib's monoidal structure on presheaves of modules requires. Nothing here relates `w`
to the size of the site.

This file does **not** contain Tag 0B8N (b) itself. It is proved elsewhere, as
`Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleSummandNoSliceSheafify.lean`, carrying
`@[stacks 0B8N "(b), invertible_local_summand"]`), with no sheafification hypothesis on the slice
sites. What is missing *here* is the
comparison of the restriction of a tensor product of presheaves of modules to a slice site with
the tensor product of the restrictions.
Objectwise the two agree definitionally, but the restriction maps do not reduce to each other
within the heartbeat limit, so the comparison has to be constructed on `tmul` generators. All
the other slice-site identifications the statement needs are definitional and are recorded
above.

## References

* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/
@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

universe v u w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {K : PresheafOfModules.{w} R.obj} {A : SheafOfModules.{w} R}

/-- The sieve of arrows along which a section `s` of `A` restricts into the image of `ψ`. -/
def imgSieve (ψ : K ⟶ A.val) {X : Cᵒᵖ} (s : A.val.obj X) : Sieve X.unop where
  arrows V i := ∃ t : K.obj (op V), ψ.app (op V) t = A.val.map i.op s
  downward_closed := by
    rintro V W i ⟨t, ht⟩ j
    exact ⟨K.map j.op t, by
      rw [PresheafOfModules.naturality_apply, ht, op_comp,
        PresheafOfModules.map_comp_apply]⟩

/-- `imgSieve ψ s` is the image sieve of `s` under the underlying morphism of presheaves of
abelian groups of `ψ`. -/
lemma imgSieve_eq (ψ : K ⟶ A.val) {X : Cᵒᵖ} (s : A.val.obj X) :
    imgSieve ψ s = Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map ψ) s := rfl

/-- Pulling back `imgSieve ψ s` along `f` gives the image sieve of the restriction of `s`
along `f`. -/
lemma imgSieve_pullback (ψ : K ⟶ A.val) {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : A.val.obj X) :
    (imgSieve ψ s).pullback f.unop = imgSieve ψ (X := Y) (A.val.map f s) := by
  ext W j
  change (∃ _, _) ↔ (∃ _, _)
  rw [← PresheafOfModules.map_comp_apply]
  exact Iff.rfl

/-- The sections of `A` which locally lie in the image of `ψ`. -/
noncomputable def localImage (ψ : K ⟶ A.val) : A.Submodule where
  obj X :=
    { carrier := {s | imgSieve ψ s ∈ J X.unop}
      add_mem' := by
        intro s t hs ht
        refine J.superset_covering ?_ (J.intersection_covering hs ht)
        rintro V i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        exact ⟨a + b, by rw [map_add, map_add, ha, hb]; rfl⟩
      zero_mem' := by
        refine J.superset_covering ?_ (J.top_mem _)
        intro V i _
        exact ⟨0, by rw [map_zero, map_zero]; rfl⟩
      smul_mem' := by
        intro r s hs
        refine J.superset_covering ?_ hs
        rintro V i ⟨a, ha⟩
        refine ⟨(R.obj.map i.op) r • a, ?_⟩
        rw [(ψ.app (op V)).hom.map_smul, ha]
        exact (A.val.map_smul i.op r s).symm }
  map := fun {X Y} f s hs => by
    change imgSieve ψ (X := Y) (A.val.map f s) ∈ J Y.unop
    rw [← imgSieve_pullback ψ f]
    exact J.pullback_stable f.unop hs
  isSheaf := fun {X} s hs => by
    refine J.transitive hs _ fun V i hi => ?_
    change (imgSieve ψ s).pullback (i.op).unop ∈ J V
    rw [imgSieve_pullback ψ i.op]
    exact hi

/-- The factorization of `ψ` through the submodule of sections locally in its image. -/
noncomputable def toLocalImage (ψ : K ⟶ A.val) : K ⟶ (localImage ψ).toPresheafOfModules where
  app X := ModuleCat.ofHom (((ψ.app X).hom).codRestrict ((localImage ψ).obj X) fun t =>
    J.superset_covering (fun V i _ => ⟨K.map i.op t, PresheafOfModules.naturality_apply ψ i.op t⟩)
      (J.top_mem _))
  naturality {X Y} f := by
    ext x
    exact Subtype.ext (PresheafOfModules.naturality_apply ψ f x)

/-- `toLocalImage ψ` followed by the inclusion of the local image is `ψ`. -/
@[simp]
lemma toLocalImage_ι (ψ : K ⟶ A.val) :
    toLocalImage ψ ≫ (localImage ψ).ι.val = ψ := by
  ext X x
  rfl

/-- A morphism from a presheaf of modules to a sheaf of modules which is *universal* — every
morphism to a sheaf of modules factors uniquely through it, i.e. `ψ` exhibits `A` as the
sheafification of `K` — is locally surjective. No sheafification instance is needed: the
subsheaf of sections locally in the image of `ψ` receives a retraction of its own inclusion
from the universal property, and the inclusion is a monomorphism. -/
theorem isLocallySurjective_of_universal (ψ : K ⟶ A.val)
    (h : ∀ S : SheafOfModules.{w} R, Function.Bijective fun g : A ⟶ S => ψ ≫ g.val) :
    PresheafOfModules.IsLocallySurjective J ψ := by
  obtain ⟨g, hg⟩ := (h (localImage ψ).toSheafOfModules).surjective (toLocalImage ψ)
  have hg' : ψ ≫ g.val = toLocalImage ψ := hg
  have h1 : g ≫ (localImage ψ).ι = 𝟙 A := by
    refine (h A).injective ?_
    change ψ ≫ g.val ≫ (localImage ψ).ι.val = ψ ≫ 𝟙 A.val
    rw [← Category.assoc, hg', Category.comp_id]
    exact toLocalImage_ι ψ
  refine ⟨fun {U} s => ?_⟩
  have h4 : ((localImage ψ).ι.val.app (op U)) (g.val.app (op U) s) = s :=
    congrArg (fun φ : A ⟶ A => φ.val.app (op U) s) h1
  have h3 : imgSieve ψ (((localImage ψ).ι.val.app (op U)) (g.val.app (op U) s)) ∈ J U :=
    (g.val.app (op U) s).2
  rw [h4] at h3
  exact h3

section Splitting

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}

section Pairing

variable (Lp Np : PresheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))

/-- Tensoring on the right with a global section `t`: `x ↦ x ⊗ t`. -/
noncomputable def coev (t : Np.sections) : Lp ⟶ Lp ⊗ Np :=
  (ρ_ Lp).inv ≫ Lp ◁ (PresheafOfModules.unitHomEquiv Np).symm t

/-- Contracting against a global section `s` of `Lp` through the pairing `ψ`. -/
noncomputable def contract
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (s : Lp.sections) : Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)) :=
  (λ_ Np).inv ≫ ((PresheafOfModules.unitHomEquiv Lp).symm s ▷ Np) ≫ ψ

/-- The projection `Lp ⊗ Np ⟶ Lp` built from a global section of `Lp` and the pairing. -/
noncomputable def proj
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (s : Lp.sections) : Lp ⊗ Np ⟶ Lp :=
  Lp ◁ contract Lp Np ψ s ≫ (ρ_ Lp).hom

/-- The morphism out of the unit attached to a global section `t` sends `1` to the value of
`t`. -/
lemma unitHomEquiv_symm_app_one (M : PresheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    (t : M.sections) (W : Cᵒᵖ) :
    (M.unitHomEquiv.symm t).app W (1 : O.obj W) = t.eval W :=
  congrArg (fun z : M.sections ↦ z.eval W) (M.unitHomEquiv.apply_symm_apply t)

/-- On sections, `coev Lp Np t` is `v ↦ v ⊗ₜ t`. -/
lemma coev_app (t : Np.sections) (W : Cᵒᵖ) (v : Lp.obj W) :
    (coev Lp Np t).app W v = v ⊗ₜ t.eval W := by
  rw [show (coev Lp Np t).app W v
      = v ⊗ₜ (Np.unitHomEquiv.symm t).app W (1 : O.obj W) from rfl,
    unitHomEquiv_symm_app_one]

/-- On sections, `contract Lp Np ψ s` is `z ↦ ψ (s ⊗ₜ z)`. -/
lemma contract_app
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (s : Lp.sections) (W : Cᵒᵖ) (z : Np.obj W) :
    (contract Lp Np ψ s).app W z = ψ.app W (s.eval W ⊗ₜ z) := by
  rw [show (contract Lp Np ψ s).app W z
      = ψ.app W ((Lp.unitHomEquiv.symm s).app W (1 : O.obj W) ⊗ₜ z) from rfl,
    unitHomEquiv_symm_app_one]

/-- `coev Lp Np t` followed by `proj Lp Np ψ s` is multiplication by the pairing `c` of `s`
and `t`. -/
lemma coev_proj_app
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (s : Lp.sections) (t : Np.sections) (W : Cᵒᵖ) (v : Lp.obj W)
    (c : O.obj W) (hc : ψ.app W (s.eval W ⊗ₜ t.eval W) = c) :
    (coev Lp Np t ≫ proj Lp Np ψ s).app W v = c • v := by
  have h1 : (coev Lp Np t ≫ proj Lp Np ψ s).app W v
      = (ρ_ (Lp.obj W)).hom (v ⊗ₜ (contract Lp Np ψ s).app W
          ((Np.unitHomEquiv.symm t).app W (1 : O.obj W))) := rfl
  rw [h1, unitHomEquiv_symm_app_one, contract_app, hc,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply]

end Pairing

/-- **Stacks Project, Tag 0B8N (b), algebraic core.** A *dual basis* for a locally bijective
pairing `ψ : L ⊗ N ⟶ O` — finitely many global sections `x j` of `L` and `y j` of `N` whose
pairings `c j` sum to `1` — exhibits `L` as a direct summand of a finite free module.

The retraction comes from the universal property of `ψ`: because `ψ` is locally bijective and
`L` is a sheaf, every morphism of presheaves of modules `L ⊗ N ⟶ L` factors uniquely through
`ψ`, and the factorisation of `proj ψ (x j)` is the `j`-th component of the retraction. No
sheafified tensor product of sheaves of modules is used, and the pairing is only required to be
a morphism of *presheaves* of modules. -/
theorem isSplitMono_of_dualBasis [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallySurjective J ψ] [PresheafOfModules.IsLocallyInjective J ψ]
    {n : ℕ} (x : Fin n → Lp.sections) (y : Fin n → Np.sections)
    (c : ∀ W : Cᵒᵖ, Fin n → O.obj W)
    (hc : ∀ (W : Cᵒᵖ) (j : Fin n), ψ.app W ((x j).eval W ⊗ₜ (y j).eval W) = c W j)
    (hsum : ∀ W : Cᵒᵖ, ∑ j, c W j = 1) :
    ∃ s : (⟨Lp, hLp⟩ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO)) ⟶
        ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
      IsSplitMono s := by
  classical
  set L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
    ⟨Lp, hLp⟩ with hL
  set E := PresheafOfModules.homEquivOfIsLocallyBijective ψ hLp with hE
  let α : Fin n → (L ⟶ SheafOfModules.unit
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :=
    fun j ↦ ⟨coev Lp Np (y j) ≫ ψ⟩
  let ρ : Fin n → (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
    hO) ⟶ L) :=
    fun j ↦ ⟨E.symm (proj Lp Np ψ (x j))⟩
  have hρ : ∀ j, ψ ≫ (ρ j).val = proj Lp Np ψ (x j) := fun j ↦ E.apply_symm_apply _
  have key : ∑ j, α j ≫ ρ j = 𝟙 L := by
    refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun W ↦
      ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_))
    have hj : ∀ j : Fin n, (α j ≫ ρ j).val.app W v = c W j • v := fun j ↦ by
      change ((coev Lp Np (y j) ≫ ψ) ≫ (ρ j).val).app W v = _
      rw [Category.assoc, hρ]
      exact coev_proj_app Lp Np ψ (x j) (y j) W v (c W j) (hc W j)
    rw [app_sum Finset.univ (fun j ↦ α j ≫ ρ j) W v,
      Finset.sum_congr rfl (fun j _ ↦ hj j), ← Finset.sum_smul, hsum W, one_smul]
    rfl
  refine ⟨Pi.lift α, ⟨⟨∑ j, Pi.π _ j ≫ ρ j, ?_⟩⟩⟩
  rw [Preadditive.comp_sum]
  simpa only [← Category.assoc, Pi.lift_π] using key

end Splitting

section Slice

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)}

/-- Restriction of presheaves of modules to the slice site over an object `V`, as a monoidal
functor. -/
noncomputable abbrev sliceFunctor (V : C) :
    PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O) ⥤
      PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        ((Over.forget V).op ⋙ O)) :=
  PresheafOfModules.pushforward₀OfCommRingCat.{w} (Over.forget V) O

/-- The ring presheaf of the slice site is the restriction of the ring presheaf. -/
lemma structureRingPresheaf_comp_forget (V : C) :
    Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf ((Over.forget V).op ⋙ O)
      = (Over.forget V).op ⋙ Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O :=
        rfl

/-- The structure sheaf of the slice site is the restriction of the structure sheaf. -/
lemma structureSheaf_comp_forget (V : C)
    (hO' : Presheaf.IsSheaf (J.over V)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf ((Over.forget V).op ⋙ O))) :
    Stacks.SheafOfModules.TensorSheafification.structureSheaf ((Over.forget V).op ⋙ O) hO'
      = (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).over V := rfl

/-- Restriction to a slice site takes the monoidal unit to the monoidal unit. -/
lemma sliceFunctor_unit (V : C) :
    (sliceFunctor (O := O) V).obj (𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
      = 𝟙_ (PresheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf ((Over.forget V).op ⋙
            O))) := rfl

/-- The underlying presheaf of modules of the restriction of a sheaf of modules to a slice site
is the restriction of its underlying presheaf of modules. -/
lemma over_val (V : C) (L : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (L.over V).val = (sliceFunctor (O := O) V).obj L.val := rfl

end Slice

end Stacks.SheafOfModules

end
