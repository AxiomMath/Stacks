module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Predeformation.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The deformation category of a point is a predeformation category

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `Λ` be a
ring with a morphism `Spec Λ ⟶ S` and let `k` be a residue field of `Λ`. For an object `x₀` of
`𝒳` lying over `Spec k`, the category of deformations of `x₀` is cofibred in groupoids over the
category of Artinian local `Λ`-algebras with residue field `k`, and its fibre over `k` is
equivalent to the one-object category. That is, it is a predeformation category.

The proof is the one in the source. A morphism of Artinian local algebras is realized on the
site as a morphism of affine schemes over `S`, and lifting it through `𝒳` — which is possible
because `𝒳` is fibred in groupoids — produces the required deformation and the required
morphism of deformations; uniqueness of the lift gives uniqueness of the morphism. For the
fibre over `k` itself the structure morphism of a deformation lies over an isomorphism, hence
is an isomorphism, which makes that fibre a one-object category.

## Main results

* `Deformation.Artin.predeformationCategory_isPredeformationCategory`: the canonical projection
  from the deformation category of a point is a predeformation category.

## Implementation notes

The fppf topology imposes no extra condition on being fibred in groupoids, so none of it enters
the argument. The fibred category lives over the size-bounded big fppf site, so realizing an
Artinian local algebra on the site needs a bound on the size of its spectrum: the cardinality
of an Artinian local ring is bounded by the cardinality of its residue field together with
`ℵ₀`, because such a ring has finite length over itself. That bound is established here as
`mk_le_of_finiteLength`, and it is what lets `siteSpecObj` place `Spec A` in the site.

The lifting and uniqueness arguments for the cofibration condition, and the computation of the
fibre over `k`, are carried out in the three auxiliary lemmas below rather than inline, so that
each is elaborated on its own.

## References

* [Stacks Project, Tag 07T5](https://stacks.math.columbia.edu/tag/07T5)
* [Stacks Project, Tag 07T4](https://stacks.math.columbia.edu/tag/07T4)
* [Stacks Project, Tag 06GS](https://stacks.math.columbia.edu/tag/06GS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Cardinal IsLocalRing

universe u v w uAux vAux

namespace Deformation.Artin

private theorem over_post_obj_injective {C : Type u} {D : Type v}
    [Category C] [Category D] (F : C ⥤ D) [F.Faithful]
    (hF : Function.Injective F.obj) {Z : C} {a b : Over Z}
    (h : (Over.post F).obj a = (Over.post F).obj b) : a = b := by
  rcases a with ⟨aL, aR, aHom⟩
  rcases b with ⟨bL, bR, bHom⟩
  change Over.mk (F.map aHom) = Over.mk (F.map bHom) at h
  have hleft : aL = bL := hF (congrArg Over.left h)
  subst bL
  have hright : aR = bR := Subsingleton.elim _ _
  subst bR
  have hpair := congrArg
    (fun o : Over (F.obj Z) => (⟨o.left, o.hom⟩ : Σ d : D, d ⟶ F.obj Z)) h
  have hmap : F.map aHom = F.map bHom := by
    injection hpair with hdom hcod
  have hhom : aHom = bHom := F.map_injective hmap
  cases hhom
  rfl

private theorem cancel_eqToHom {C : Type u} [Category.{v} C]
    {A A' B B' : C} (hA : A = A') (hB : B = B')
    {f : A ⟶ B} {g : A' ⟶ B'}
    (h : eqToHom hA.symm ≫ f ≫ eqToHom hB = g) :
    f = eqToHom hA ≫ g ≫ eqToHom hB.symm := by
  cat_disch

/-- A composite of two cast morphisms is the cast morphism of the composite equality. -/
private theorem eqToHom_comp_eqToHom_eq {𝒞 : Type uAux} [Category.{vAux} 𝒞] {X Y Z : 𝒞}
    (h₁ : X = Y) (h₂ : Y = Z) (h : X = Z) : eqToHom h₁ ≫ eqToHom h₂ = eqToHom h := by
  cases h₁
  cases h₂
  simp

/-- A morphism conjugated by a cancelling pair of cast isomorphisms on each side is itself. -/
private theorem eqToHom_conj_cancel {𝒞 : Type uAux} [Category.{vAux} 𝒞]
    {P Q X Y : 𝒞} (m : P ⟶ Q) (h₁ : P = X) (h₂ : X = P) (h₃ : Q = Y) (h₄ : Y = Q) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ m ≫ eqToHom h₃) ≫ eqToHom h₄ = m := by
  cases h₁
  cases h₃
  simp

private theorem mk_quotient_le_mul {R M : Type u} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) : #M ≤ #(M ⧸ N) * #N := by
  apply Cardinal.mk_le_mk_mul_of_mk_preimage_le (Submodule.mkQ N)
  intro q
  let x₀ : M := Classical.choose (Submodule.mkQ_surjective N q)
  have hx₀ : Submodule.mkQ N x₀ = q := Classical.choose_spec (Submodule.mkQ_surjective N q)
  let f : {x : M // Submodule.mkQ N x = q} → N := fun x => ⟨x.1 - x₀, by
    have hh : Submodule.mkQ N (x.1 - x₀) = 0 := by simp [map_sub, x.2, hx₀]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hh
    exact hh⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have hh := congrArg (fun z : N => (z : M)) h
    dsimp [f] at hh
    have hh' := congrArg (fun z : M => z + x₀) hh
    simpa using hh'
  exact Cardinal.mk_le_of_injective hf

private theorem mk_le_of_finiteLength (K A : Type u) [Field K] [CommRing A]
    [IsLocalRing A] [IsArtinianRing A] (e : ResidueField A ≃+* K) :
    #A ≤ max ℵ₀ #K := by
  let κ : Cardinal := max ℵ₀ #K
  have hκ : ℵ₀ ≤ κ := le_max_left _ _
  have hres : #(A ⧸ IsLocalRing.maximalIdeal A) ≤ κ := by
    calc
      #(A ⧸ IsLocalRing.maximalIdeal A) = #(ResidueField A) := by rfl
      _ = #K := Cardinal.mk_congr e.toEquiv
      _ ≤ κ := le_max_right _ _
  have hlen : IsFiniteLength A A :=
    (isArtinianRing_iff_isFiniteLength A).mp inferInstance
  have hgeneral : ∀ (M : Type u) [AddCommGroup M] [Module A M],
      IsFiniteLength A M → #M ≤ κ := by
    intro M _ _ hM
    refine IsFiniteLength.rec (motive := fun M _ _ _ => #M ≤ κ) ?_ ?_ hM
    · intro M _ _ _
      exact (mk_le_aleph0).trans hκ
    · intro M _ _ N hsimple hN ih
      have hsimp : #(M ⧸ N) ≤ κ := by
        obtain ⟨I, hI, ⟨eI⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
        obtain rfl := IsLocalRing.eq_maximalIdeal hI
        calc
          #(M ⧸ N) = #(A ⧸ IsLocalRing.maximalIdeal A) := Cardinal.mk_congr eI.toEquiv
          _ ≤ κ := hres
      calc
        #M ≤ #(M ⧸ N) * #N := mk_quotient_le_mul N
        _ ≤ κ * κ := mul_le_mul' hsimp ih
        _ = κ := Cardinal.mul_eq_self hκ
  exact hgeneral A hlen


private theorem spec_k_lt_cutoff (B : AlgebraicGeometry.BigFppfSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S) {Λ k : Type u}
    [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    (Spec (CommRingCat.of k)).size < B.cutoff := by
  have hleft : B.inclusion.obj (p.obj x₀).left = Spec (CommRingCat.of k) := by
    simpa [Functor.comp_obj, Over.post_obj] using congrArg Over.left hx₀
  have hsize : (B.inclusion.obj (p.obj x₀).left).size < B.cutoff :=
    (p.obj x₀).left.property
  exact hleft ▸ hsize

private theorem spec_artinian_size_lt (B : AlgebraicGeometry.BigFppfSite.{u})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hk : (Spec (CommRingCat.of k)).size < B.cutoff) :
    (Spec (CommRingCat.of A)).size < B.cutoff := by
  apply Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hk
  exact mk_le_of_finiteLength k A A.residueEquiv.toRingEquiv

private noncomputable def siteSpecObj (B : AlgebraicGeometry.BigFppfSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S) {Λ k : Type u}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff) :
    AlgebraicGeometry.BigFppfOver B S hS := by
  let X := B.obj hA
  let Y := B.obj hS
  let f : B.inclusion.obj X ⟶ B.inclusion.obj Y :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  exact Over.mk (B.inclusion.preimage f)

private noncomputable def siteSpecKObj
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hk : (Spec (CommRingCat.of k)).size < B.cutoff) :
    AlgebraicGeometry.BigFppfOver B S hS := by
  let X := B.obj hk
  let Y := B.obj hS
  let f : B.inclusion.obj X ⟶ B.inclusion.obj Y :=
    Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ
  exact Over.mk (B.inclusion.preimage f)

private theorem siteSpecKObj_post
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hk : (Spec (CommRingCat.of k)).size < B.cutoff) :
    (Over.post B.inclusion).obj (siteSpecKObj B hS iΛ hk) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) := by
  change Over.mk (B.inclusion.map (B.inclusion.preimage _)) = _
  congr 1
  exact B.inclusion.map_preimage _

private theorem siteSpecKObj_post_hom
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (hk : (Spec (CommRingCat.of k)).size < B.cutoff) :
    ((Over.post B.inclusion).obj (siteSpecKObj B hS iΛ hk)).hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
  change B.inclusion.map (B.inclusion.preimage _) = _
  exact B.inclusion.map_preimage _

private theorem siteSpecObj_post (B : AlgebraicGeometry.BigFppfSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S) {Λ k : Type u}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff) :
    (Over.post B.inclusion).obj (siteSpecObj B hS iΛ A hA) =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := by
  change Over.mk (B.inclusion.map (B.inclusion.preimage _)) = _
  congr 1
  exact B.inclusion.map_preimage _

private theorem siteSpecObj_post_hom (B : AlgebraicGeometry.BigFppfSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S) {Λ k : Type u}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff) :
    ((Over.post B.inclusion).obj (siteSpecObj B hS iΛ A hA)).hom =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := by
  change B.inclusion.map (B.inclusion.preimage _) = _
  exact B.inclusion.map_preimage _

/-- An object of the site over `S` is determined by its image under `Over.post B.inclusion`. -/
private theorem post_obj_injective (B : AlgebraicGeometry.BigFppfSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S) {a b : AlgebraicGeometry.BigFppfOver B S hS}
    (h : (Over.post B.inclusion).obj a = (Over.post B.inclusion).obj b) : a = b :=
  over_post_obj_injective B.inclusion (by
    intro a b h
    cases a
    cases b
    cases h
    rfl) h

private theorem specialPoint_baseSite
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    p.obj x₀ = siteSpecKObj B hS iΛ
      (spec_k_lt_cutoff B hS iΛ p x₀ hx₀) := by
  apply post_obj_injective B hS
  exact hx₀.trans (siteSpecKObj_post B hS iΛ
    (spec_k_lt_cutoff B hS iΛ p x₀ hx₀)).symm

/-- Precomposing the structure map of `B` with a `Λ`-algebra map gives that of `A`. -/
private theorem spec_map_comp_algebraMap {Λ A B : Type u} [CommRing Λ] [CommRing A] [CommRing B]
    [Algebra Λ A] [Algebra Λ B] {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S) (φ : A →+* B)
    (h : φ.comp (algebraMap Λ A) = algebraMap Λ B) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

private theorem residueMap_comp_algebraMap {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (Deformation.Artin.residueMap A).comp (algebraMap Λ A) = algebraMap Λ k := by
  let : IsScalarTower Λ A (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  ext r
  change A.residueEquiv (IsLocalRing.residue A (algebraMap Λ A r)) = algebraMap Λ k r
  rw [← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply Λ A (IsLocalRing.ResidueField A) r]
  exact A.residueEquiv.commutes r

private noncomputable def siteResidueMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff)
    (hk : (Spec (CommRingCat.of k)).size < B.cutoff) :
    siteSpecKObj B hS iΛ hk ⟶ siteSpecObj B hS iΛ A hA := by
  refine Over.homMk (B.inclusion.preimage
    (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)))) ?_
  simpa [siteSpecObj, siteSpecKObj, Over.hom] using B.inclusion.map_injective (by
    simp only [Functor.map_comp, Functor.map_preimage]
    exact spec_map_comp_algebraMap iΛ _ (residueMap_comp_algebraMap A))

-- The residue maps are compatible with the arrows of `𝒞_Λ`:
-- `Deformation.Artin.residueMap_comp`, public beside `Deformation.Artin.residueMap` in
-- `StacksFrontier.Deformation.Artin.Predeformation` (already in this file's closure, so no
-- import edge). A `private` re-declaration stood here.

private theorem specMap_comp_assoc
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B C : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ B) (g : B ⟶ C) {T : Scheme.{u}} (h : Spec (.of A) ⟶ T) :
    Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫ h =
      Spec.map (CommRingCat.ofHom (f ≫ g).hom.toRingHom) ≫ h := by
  rw [← Spec.map_comp_assoc]
  rfl

private noncomputable def siteSpecMap (B : AlgebraicGeometry.BigFppfSite.{u})
    {S : Scheme.{u}} (hS : B.Contains S) {Λ k : Type u}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff)
    (hA' : (Spec (CommRingCat.of A')).size < B.cutoff)
    (f : A ⟶ A') : siteSpecObj B hS iΛ A' hA' ⟶ siteSpecObj B hS iΛ A hA := by
  refine Over.homMk (B.inclusion.preimage
    (Spec.map (CommRingCat.ofHom f.hom.toRingHom))) ?_
  simpa [siteSpecObj, Over.hom] using B.inclusion.map_injective (by
    simp only [Functor.map_comp, Functor.map_preimage]
    exact spec_map_comp_algebraMap iΛ _ f.hom.comp_algebraMap)

private theorem siteResidueMap_triangle
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff)
    (hk : (Spec (CommRingCat.of k)).size < B.cutoff) :
    Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
      ((Over.post B.inclusion).obj (siteSpecObj B hS iΛ A hA)).hom =
    ((Over.post B.inclusion).obj (siteSpecKObj B hS iΛ hk)).hom := by
  rw [siteSpecObj_post_hom, siteSpecKObj_post_hom]
  exact spec_map_comp_algebraMap iΛ _ (residueMap_comp_algebraMap A)

private theorem siteResidueMap_post
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff)
    (hk : (Spec (CommRingCat.of k)).size < B.cutoff) :
    (Over.post B.inclusion).map (siteResidueMap B hS iΛ A hA hk) =
      Over.homMk (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)))
        (siteResidueMap_triangle B hS iΛ A hA hk) := by
  apply Over.OverMorphism.ext
  change B.inclusion.map (B.inclusion.preimage _) = _
  exact B.inclusion.map_preimage _

private theorem siteResidueMap_left
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff)
    (hk : (Spec (CommRingCat.of k)).size < B.cutoff) :
    B.inclusion.map (Over.Hom.left (siteResidueMap B hS iΛ A hA hk)) =
      eqToHom (congrArg Over.left (siteSpecKObj_post B hS iΛ hk)) ≫
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
        eqToHom (congrArg Over.left (siteSpecObj_post B hS iΛ A hA)).symm := by
  have h := congrArg Over.Hom.left (siteResidueMap_post B hS iΛ A hA hk)
  change (Over.Hom.left (siteResidueMap B hS iΛ A hA hk)).hom =
    eqToHom (congrArg Over.left (siteSpecKObj_post B hS iΛ hk)) ≫
      Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
      eqToHom (congrArg Over.left (siteSpecObj_post B hS iΛ A hA)).symm at h
  exact h

private theorem siteSpecMap_triangle
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff)
    (hA' : (Spec (CommRingCat.of A')).size < B.cutoff)
    (f : A ⟶ A') :
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      ((Over.post B.inclusion).obj (siteSpecObj B hS iΛ A hA)).hom =
    ((Over.post B.inclusion).obj (siteSpecObj B hS iΛ A' hA')).hom := by
  rw [siteSpecObj_post_hom, siteSpecObj_post_hom]
  exact spec_map_comp_algebraMap iΛ _ f.hom.comp_algebraMap

private theorem siteSpecMap_post
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff)
    (hA' : (Spec (CommRingCat.of A')).size < B.cutoff)
    (f : A ⟶ A') :
    (Over.post B.inclusion).map (siteSpecMap B hS iΛ hA hA' f) =
      Over.homMk (Spec.map (CommRingCat.ofHom f.hom.toRingHom))
        (siteSpecMap_triangle B hS iΛ hA hA' f) := by
  apply Over.OverMorphism.ext
  change B.inclusion.map (B.inclusion.preimage _) = _
  exact B.inclusion.map_preimage _

private theorem siteSpecMap_left
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff)
    (hA' : (Spec (CommRingCat.of A')).size < B.cutoff)
    (f : A ⟶ A') :
    B.inclusion.map (Over.Hom.left (siteSpecMap B hS iΛ hA hA' f)) =
      eqToHom (congrArg Over.left (siteSpecObj_post B hS iΛ A' hA')) ≫
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
        eqToHom (congrArg Over.left (siteSpecObj_post B hS iΛ A hA)).symm := by
  have h := congrArg Over.Hom.left (siteSpecMap_post B hS iΛ hA hA' f)
  change (Over.Hom.left (siteSpecMap B hS iΛ hA hA' f)).hom = _ at h
  exact h

private theorem siteResidueMap_comp_siteSpecMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    {A A' : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff)
    (hA' : (Spec (CommRingCat.of A')).size < B.cutoff)
    (hk : (Spec (CommRingCat.of k)).size < B.cutoff)
    (f : A ⟶ A') :
    siteResidueMap B hS iΛ A' hA' hk ≫
      siteSpecMap B hS iΛ hA hA' f =
    siteResidueMap B hS iΛ A hA hk := by
  apply (Over.post B.inclusion).map_injective
  rw [Functor.map_comp, siteResidueMap_post, siteSpecMap_post,
    siteResidueMap_post]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A')) ≫
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) =
    Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (residueMap_comp f)

private theorem deformationPoint_baseSite
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (d : Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀) :
    p.obj d.point = siteSpecObj B hS iΛ d.algebra
      (spec_artinian_size_lt B d.algebra
        (spec_k_lt_cutoff B hS iΛ p x₀ hx₀)) := by
  apply post_obj_injective B hS
  exact d.base.trans (siteSpecObj_post B hS iΛ d.algebra
    (spec_artinian_size_lt B d.algebra
      (spec_k_lt_cutoff B hS iΛ p x₀ hx₀))).symm

private theorem siteSpecMap_transport_left
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (a b : Deformation.Artin.DeformationObject iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀)
    (ha : (Spec (CommRingCat.of a.algebra)).size < B.cutoff)
    (hb : (Spec (CommRingCat.of b.algebra)).size < B.cutoff)
    (haPoint : p.obj a.point = siteSpecObj B hS iΛ a.algebra ha)
    (hbPoint : p.obj b.point = siteSpecObj B hS iΛ b.algebra hb)
    (g : a.algebra ⟶ b.algebra) :
    B.inclusion.map (Over.Hom.left
      (eqToHom hbPoint ≫ siteSpecMap B hS iΛ ha hb g ≫ eqToHom haPoint.symm)) =
      eqToHom (congrArg Over.left b.base) ≫
        Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
        eqToHom (congrArg Over.left a.base).symm := by
  let haPost := (congrArg ((Over.post B.inclusion).obj) haPoint).trans
    (siteSpecObj_post B hS iΛ a.algebra ha)
  let hbPost := (congrArg ((Over.post B.inclusion).obj) hbPoint).trans
    (siteSpecObj_post B hS iΛ b.algebra hb)
  have hbTransportForward :
      B.inclusion.map (eqToHom (congrArg Over.left hbPoint)) ≫
        eqToHom (congrArg Over.left (siteSpecObj_post B hS iΛ b.algebra hb)) =
      eqToHom (congrArg Over.left hbPost) := by
    rw [eqToHom_map]
    exact eqToHom_comp_eqToHom_eq (𝒞 := Scheme.{u}) _ _ _
  have haTransportBackward :
      eqToHom (congrArg Over.left (siteSpecObj_post B hS iΛ a.algebra ha)).symm ≫
        B.inclusion.map (eqToHom (congrArg Over.left haPoint).symm) =
      eqToHom (congrArg Over.left haPost).symm := by
    rw [eqToHom_map]
    exact eqToHom_comp_eqToHom_eq (𝒞 := Scheme.{u}) _ _ _
  have h1 : B.inclusion.map (Over.Hom.left (eqToHom hbPoint)) ≫
      B.inclusion.map (Over.Hom.left (siteSpecMap B hS iΛ ha hb g)) ≫
      B.inclusion.map (Over.Hom.left (eqToHom haPoint.symm)) =
      (B.inclusion.map (Over.Hom.left (eqToHom hbPoint)) ≫
        eqToHom (congrArg Over.left
          (siteSpecObj_post B hS iΛ b.algebra hb))) ≫
      Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
      (eqToHom (congrArg Over.left
          (siteSpecObj_post B hS iΛ a.algebra ha)).symm ≫
        B.inclusion.map (Over.Hom.left (eqToHom haPoint.symm))) := by
    rw [siteSpecMap_left]
    cat_disch
  have h2 : (B.inclusion.map (Over.Hom.left (eqToHom hbPoint)) ≫
        eqToHom (congrArg Over.left
          (siteSpecObj_post B hS iΛ b.algebra hb))) ≫
      Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
      (eqToHom (congrArg Over.left
          (siteSpecObj_post B hS iΛ a.algebra ha)).symm ≫
        B.inclusion.map (Over.Hom.left (eqToHom haPoint.symm))) =
      eqToHom (congrArg Over.left hbPost) ≫
        Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
        eqToHom (congrArg Over.left haPost).symm := by
    simp only [Over.eqToHom_left]
    rw [hbTransportForward, haTransportBackward]
  exact h1.trans h2

/-- The left component of the arrow of a deformation lies over the residue map. -/
private theorem deformationObject_arrow_left {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S} {X : Type v} [Category.{w} X] {q : X ⥤ Over S}
    {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (d : Deformation.Artin.DeformationObject iΛ q x₀ hx₀) :
    (q.map d.arrow).left =
      eqToHom (congrArg Over.left hx₀) ≫
        Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap d.algebra)) ≫
        eqToHom (congrArg Over.left d.base).symm :=
  cancel_eqToHom (congrArg Over.left hx₀) (congrArg Over.left d.base) d.arrow_base

/-- The left component of the reversed arrow of a deformation morphism lies over its ring map. -/
private theorem deformationMorphism_arrow_left {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S} {X : Type v} [Category.{w} X]
    {q : X ⥤ Over S} {x₀ : X} {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (m : Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b) :
    (q.map m.arrow).left =
      eqToHom (congrArg Over.left b.base) ≫ Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
        eqToHom (congrArg Over.left a.base).symm :=
  cancel_eqToHom (congrArg Over.left b.base) (congrArg Over.left a.base) m.arrow_base


/-- The deformation with algebra `A` obtained from an arrow `χ` out of `x₀` lying over the
residue map. -/
private noncomputable def deformationObjectOfLift
    (B : AlgebraicGeometry.BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) {X : Type v} [Category.{w} X]
    (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS) (x₀ : X)
    (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : (Spec (CommRingCat.of A)).size < B.cutoff) {y : X} (χ : x₀ ⟶ y)
    (hy : p.obj y = siteSpecObj B hS iΛ A hA)
    (hχ : p.map χ = eqToHom (specialPoint_baseSite B hS iΛ p x₀ hx₀) ≫
      siteResidueMap B hS iΛ A hA (spec_k_lt_cutoff B hS iΛ p x₀ hx₀) ≫ eqToHom hy.symm) :
    Deformation.Artin.DeformationObject iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀ where
  algebra := A
  point := y
  arrow := χ
  base := (congrArg (Over.post B.inclusion).obj hy).trans (siteSpecObj_post B hS iΛ A hA)
  arrow_base := by
    rw [Functor.comp_map, hχ]
    have hrleft : ((Over.post B.inclusion).map (siteResidueMap B hS iΛ A hA
        (spec_k_lt_cutoff B hS iΛ p x₀ hx₀))).left = _ :=
      siteResidueMap_left B hS iΛ A hA (spec_k_lt_cutoff B hS iΛ p x₀ hx₀)
    simp only [Functor.map_comp, Over.comp_left]
    rw [hrleft]
    have hsource : congrArg Over.left hx₀ = congrArg Over.left (congrArg
        (Over.post B.inclusion).obj (specialPoint_baseSite B hS iΛ p x₀ hx₀)) :=
      Subsingleton.elim _ _
    rw [hsource]
    simp only [eqToHom_map, Over.eqToHom_left, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Category.comp_id]

variable (B : AlgebraicGeometry.BigFppfSite.{u})
variable {S : Scheme.{u}} (hS : B.Contains S)
variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (iΛ : Spec (.of Λ) ⟶ S)
variable {X : Type v} [Category.{w} X]
variable (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
variable (x₀ : X)
variable (hx₀ : (p ⋙ Over.post B.inclusion).obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

private theorem fibered_hom_ext {D E : Type*} [Category D] [Category E]
    {q : D ⥤ E} (hq : q.IsFiberedInGroupoids) {a b c : D}
    (f g : a ⟶ b) (h : b ⟶ c) (hmap : q.map f = q.map g)
    (hcomp : f ≫ h = g ≫ h) : f = g := by
  obtain ⟨l, hl, hu⟩ := hq.unique_lift h (g ≫ h) (q.map g) (by simp)
  exact (hu f ⟨hmap, hcomp⟩).trans (hu g ⟨rfl, rfl⟩).symm


private theorem residueMap_residueFieldObject
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] :
    Deformation.Artin.residueMap (Deformation.residueFieldObject.{u,u,u} Λ k) =
      ULift.ringEquiv.toRingHom := by
  ext a
  rfl

private theorem fibered_isIso {D E : Type*} [Category D] [Category E]
    {q : D ⥤ E} (hq : q.IsFiberedInGroupoids) {a b : D}
    (f : a ⟶ b) [IsIso (q.map f)] : IsIso f := by
  let := hq.isStronglyCartesian f
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := q) (f := q.map f) f

private noncomputable def deformationMorphismOfIsIso
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type v} [Category.{w} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀)
    (g : a.algebra ⟶ b.algebra) [IsIso b.arrow] :
    Deformation.Artin.DeformationMorphism iΛ q x₀ hx₀ a b where
  ringHom := g
  arrow := inv b.arrow ≫ a.arrow
  triangle := by simp
  arrow_base := by
    have : IsIso (q.map b.arrow).left :=
      inferInstanceAs (IsIso ((Over.forget S).map (q.map b.arrow)))
    have ha := deformationObject_arrow_left a
    have hb := deformationObject_arrow_left b
    have hcomp : (q.map b.arrow).left ≫
        (eqToHom (congrArg Over.left b.base) ≫
          Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
          eqToHom (congrArg Over.left a.base).symm) = (q.map a.arrow).left := by
      rw [ha, hb]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, residueMap_comp]
    have hh : (q.map (inv b.arrow ≫ a.arrow)).left =
        eqToHom (congrArg Over.left b.base) ≫
          Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
          eqToHom (congrArg Over.left a.base).symm := by
      apply (cancel_epi (q.map b.arrow).left).mp
      rw [hcomp, ← Over.comp_left, ← Functor.map_comp]
      simp
    rw [hh]
    simp

/-- The canonical deformation category of a point of a fibred category is a
predeformation category. -/
@[stacks 07T5]
public theorem predeformationCategory_isPredeformationCategory
    (hp : p.IsFiberedInGroupoids) :
    let C := Deformation.Artin.predeformationCategory iΛ
      (p ⋙ Over.post B.inclusion) x₀ hx₀
    letI : Category C.carrier := C.category
    Deformation.IsPredeformationCategory C.projection := by
  let C := Deformation.Artin.predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x₀ hx₀
  let : Category C.carrier := C.category
  have construction_projection_map {a b : C.carrier} (f : a ⟶ b) :
      C.projection.map f = eqToHom (C.object_projection a) ≫
        (C.morphisms a b f).ringHom ≫ eqToHom (C.object_projection b).symm := by
    have h := C.morphism_projection f
    rw [← h]
    simp
  change Deformation.IsPredeformationCategory C.projection
  refine ⟨?_, ?_⟩
  · change C.projection.op.IsFiberedInGroupoids
    refine { exists_lift := ?_, unique_lift := ?_ }
    · intro V U f x hx
      let d := C.objects x.unop
      have hxA : d.algebra = U.unop := by
        calc
          d.algebra = C.projection.obj x.unop := (C.object_projection _).symm
          _ = U.unop := congrArg Opposite.unop hx
      let hk := spec_k_lt_cutoff B hS iΛ p x₀ hx₀
      have hA : (Spec (CommRingCat.of d.algebra)).size < B.cutoff :=
        spec_artinian_size_lt B d.algebra hk
      have hA' : (Spec (CommRingCat.of V.unop)).size < B.cutoff :=
        spec_artinian_size_lt B V.unop hk
      let g : d.algebra ⟶ V.unop := eqToHom hxA ≫ f.unop
      let s : siteSpecObj B hS iΛ V.unop hA' ⟶
          siteSpecObj B hS iΛ d.algebra hA :=
        siteSpecMap B hS iΛ hA hA' g
      have hpoint := deformationPoint_baseSite B hS iΛ p x₀ hx₀ d
      obtain ⟨y, ψ, hψ⟩ := hp.exists_lift s d.point hpoint
      let a'Obj := siteSpecObj B hS iΛ V.unop hA'
      have hx0site := specialPoint_baseSite B hS iΛ p x₀ hx₀
      have hySite : p.obj y = a'Obj := by
        dsimp [a'Obj]
        have h := IsHomLift.domain_eq p s ψ
        simpa [s] using h
      let r := siteResidueMap B hS iΛ V.unop hA' hk
      let r' : p.obj x₀ ⟶ p.obj y :=
        eqToHom hx0site ≫ r ≫ eqToHom hySite.symm
      have hcomm : r' ≫ p.map ψ = p.map d.arrow := by
        apply (Over.post B.inclusion).map_injective
        apply Over.OverMorphism.ext
        let : p.IsHomLift s ψ := hψ
        have hfac := IsHomLift.fac' p s ψ
        rw [show IsHomLift.domain_eq p s ψ = hySite from Subsingleton.elim _ _,
          show IsHomLift.codomain_eq p s ψ = hpoint from Subsingleton.elim _ _] at hfac
        rw [hfac]
        change B.inclusion.map (Over.Hom.left r') ≫
          (B.inclusion.map (Over.Hom.left (eqToHom hySite)) ≫
            B.inclusion.map (Over.Hom.left s) ≫
            B.inclusion.map (Over.Hom.left (eqToHom hpoint.symm))) =
          B.inclusion.map (Over.Hom.left (p.map d.arrow))
        have hres := siteResidueMap_comp_siteSpecMap B hS iΛ hA hA' hk g
        have harrow : B.inclusion.map (p.map d.arrow).left = _ :=
          deformationObject_arrow_left (q := p ⋙ Over.post B.inclusion) d
        have hresLeft := congrArg
          (fun f : siteSpecKObj B hS iΛ hk ⟶
              siteSpecObj B hS iΛ d.algebra hA => (Over.Hom.left f).hom) hres
        have hresLeft' :
            (Over.Hom.left r).hom ≫ (Over.Hom.left s).hom =
              (Over.Hom.left
                (siteResidueMap B hS iΛ d.algebra hA hk)).hom := by
          change (Over.Hom.left (r ≫ s)).hom = _
          exact hresLeft
        have hmid : (Over.Hom.left r).hom ≫ (Over.Hom.left s).hom =
            eqToHom (congrArg Over.left (siteSpecKObj_post B hS iΛ hk)) ≫
              Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap d.algebra)) ≫
              eqToHom (congrArg Over.left
                (siteSpecObj_post B hS iΛ d.algebra hA)).symm := by
          calc
            _ = (Over.Hom.left
                (siteResidueMap B hS iΛ d.algebra hA hk)).hom := hresLeft'
            _ = _ := by
              exact siteResidueMap_left B hS iΛ d.algebra hA hk
        calc
          _ = (Over.Hom.left (eqToHom hx0site)).hom ≫
              (Over.Hom.left r).hom ≫ (Over.Hom.left s).hom ≫
              (Over.Hom.left (eqToHom hpoint.symm)).hom := by
                simp [r', Category.assoc]
          _ = (Over.Hom.left (eqToHom hx0site)).hom ≫
              ((Over.Hom.left r).hom ≫ (Over.Hom.left s).hom) ≫
              (Over.Hom.left (eqToHom hpoint.symm)).hom := by cat_disch
          _ = (Over.Hom.left (eqToHom hx0site)).hom ≫
              Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap d.algebra)) ≫
              (Over.Hom.left (eqToHom hpoint.symm)).hom := by
                rw [hmid]
                cat_disch
          _ = B.inclusion.map (Over.Hom.left (p.map d.arrow)) := by
            have hh : ∀ {𝒟 : Type (u + 1)} [Category.{u} 𝒟] {P : ObjectProperty 𝒟}
                {a b : P.FullSubcategory} (h : a = b),
                (eqToHom h).hom = eqToHom (congrArg (·.obj) h) := by
              intro _ _ _ a b h; subst h; rfl
            convert harrow.symm using 1
            all_goals first
              | rfl
              | (simp only [Over.eqToHom_left, hh]; rfl)
      obtain ⟨χ, ⟨hχmap, hχcomp⟩, hχuniq⟩ :=
        hp.unique_lift ψ d.arrow r' hcomm
      let e := deformationObjectOfLift B hS iΛ p x₀ hx₀ V.unop hA' χ hySite hχmap
      obtain ⟨z, hze⟩ := C.objects.surjective e
      let m₀ : Deformation.Artin.DeformationMorphism iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀ d e := {
        ringHom := g
        arrow := ψ
        triangle := by
          exact hχcomp
        arrow_base := by
          have hfac := IsHomLift.fac' p s ψ
          have hleft := siteSpecMap_transport_left B hS iΛ p x₀ hx₀
            d e hA hA' hpoint hySite g
          have hmap : B.inclusion.map (p.map ψ).left =
              eqToHom (congrArg Over.left e.base) ≫
                Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
                eqToHom (congrArg Over.left d.base).symm := by
            rw [hfac]
            exact hleft
          change eqToHom (congrArg Over.left e.base).symm ≫
            B.inclusion.map (p.map ψ).left ≫ eqToHom (congrArg Over.left d.base) = _
          erw [hmap]
          exact eqToHom_conj_cancel (𝒞 := Scheme.{u}) _ _ _ _ _
      }
      let m : Deformation.Artin.DeformationMorphism iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀ d (C.objects z) :=
        transportDeformationMorphism rfl hze m₀
      let m' : x.unop ⟶ z := (C.morphisms (x.unop) z).symm m
      refine ⟨Opposite.op z, Opposite.op m', ?_⟩
      have hz : C.projection.obj z = V.unop := by
        calc
          C.projection.obj z = (C.objects z).algebra := C.object_projection z
          _ = e.algebra := congrArg Deformation.Artin.DeformationObject.algebra hze
          _ = V.unop := rfl
      have hx' : C.projection.obj x.unop = U.unop :=
        (C.object_projection x.unop).trans hxA
      apply IsHomLift.of_fac C.projection.op f (Opposite.op m')
        (congrArg Opposite.op hz) (congrArg Opposite.op hx')
      have hm : C.morphisms (x.unop) z m' = m := by
        exact (C.morphisms (x.unop) z).apply_symm_apply m
      have hprojection : C.projection.map m' =
          eqToHom (C.object_projection x.unop) ≫ m.ringHom ≫
            eqToHom (C.object_projection z).symm := by
        rw [construction_projection_map m', hm]
      apply Quiver.Hom.unop_inj
      simp only [unop_comp, eqToHom_unop, Functor.op_map]
      change f.unop = eqToHom hx'.symm ≫ C.projection.map m' ≫ eqToHom hz
      have hRing : m.ringHom ≫
          eqToHom (congrArg Deformation.Artin.DeformationObject.algebra hze) = g := by
        change (transportDeformationMorphism rfl hze m₀).ringHom ≫
          eqToHom (congrArg Deformation.Artin.DeformationObject.algebra hze) = g
        simp [transportDeformationMorphism_ringHom]
        rfl
      have hsourceCast : eqToHom hx'.symm ≫
          eqToHom (C.object_projection x.unop) = eqToHom hxA.symm := by
        calc
          _ = eqToHom (hx'.symm.trans (C.object_projection x.unop)) := by
            rw [eqToHom_trans]
          _ = _ := congrArg eqToHom (Subsingleton.elim _ _)
      have htargetCast : eqToHom (C.object_projection z).symm ≫
          eqToHom hz = eqToHom
            (congrArg Deformation.Artin.DeformationObject.algebra hze) := by
        calc
          _ = eqToHom ((C.object_projection z).symm.trans hz) := by
            rw [eqToHom_trans]
          _ = _ := congrArg eqToHom (Subsingleton.elim _ _)
      calc
        f.unop = eqToHom hxA.symm ≫ g := by
          dsimp [g]
          cat_disch
        _ = eqToHom hx'.symm ≫ C.projection.map m' ≫ eqToHom hz := by
          rw [hprojection]
          calc
            _ = eqToHom hxA.symm ≫ (m.ringHom ≫
                eqToHom (congrArg Deformation.Artin.DeformationObject.algebra hze)) := by
              rw [hRing]
              rfl
            _ = _ := by
              conv_lhs =>
                rw [← hsourceCast, ← htargetCast]
              cat_disch
    · intro x y z phi psi f hf
      let x' := Opposite.unop x
      let y' := Opposite.unop y
      let z' := Opposite.unop z
      have hbase : C.projection.map (Quiver.Hom.unop phi) ≫ f.unop =
          C.projection.map (Quiver.Hom.unop psi) := by
        have hf' := congrArg Quiver.Hom.unop hf
        simpa only [unop_comp, Functor.op_map, Functor.op_obj,
          Opposite.unop_op, Quiver.Hom.unop_op] using hf'
      let dx := C.objects x'
      let dy := C.objects y'
      let dz := C.objects z'
      let mphi := C.morphisms x' y' (Quiver.Hom.unop phi)
      let mpsi := C.morphisms x' z' (Quiver.Hom.unop psi)
      let g : dy.algebra ⟶ dz.algebra :=
        eqToHom (C.object_projection y').symm ≫ f.unop ≫
          eqToHom (C.object_projection z')
      have hRing : mphi.ringHom ≫ g = mpsi.ringHom := by
        have hφ := construction_projection_map (Quiver.Hom.unop phi)
        have hψ := construction_projection_map (Quiver.Hom.unop psi)
        rw [hφ, hψ] at hbase
        dsimp [mphi, mpsi, g]
        have hbase' : eqToHom (C.object_projection x') ≫
            (((C.morphisms x' y') (Quiver.Hom.unop phi)).ringHom ≫
              eqToHom (C.object_projection y').symm ≫ f.unop) =
            eqToHom (C.object_projection x') ≫
              ((C.morphisms x' z') (Quiver.Hom.unop psi)).ringHom ≫
                eqToHom (C.object_projection z').symm := by
          simpa [Category.assoc] using hbase
        have hmid := (cancel_epi (eqToHom (C.object_projection x'))).mp hbase'
        calc
          _ = (((C.morphisms x' y') (Quiver.Hom.unop phi)).ringHom ≫
                eqToHom (C.object_projection y').symm ≫ f.unop) ≫
              eqToHom (C.object_projection z') := by cat_disch
          _ = (((C.morphisms x' z') (Quiver.Hom.unop psi)).ringHom ≫
                eqToHom (C.object_projection z').symm) ≫
              eqToHom (C.object_projection z') := by rw [hmid]
          _ = (C.morphisms x' z' (Quiver.Hom.unop psi)).ringHom := by simp
      let hdy := spec_artinian_size_lt B dy.algebra
        (spec_k_lt_cutoff B hS iΛ p x₀ hx₀)
      let hdz := spec_artinian_size_lt B dz.algebra
        (spec_k_lt_cutoff B hS iΛ p x₀ hx₀)
      let hY := deformationPoint_baseSite B hS iΛ p x₀ hx₀ dy
      let hZ := deformationPoint_baseSite B hS iΛ p x₀ hx₀ dz
      let s := eqToHom hZ ≫ siteSpecMap B hS iΛ hdy hdz g ≫ eqToHom hY.symm
      have hsLeft := siteSpecMap_transport_left B hS iΛ p x₀ hx₀
        dy dz hdy hdz hY hZ g
      have hphiLeft : B.inclusion.map (p.map mphi.arrow).left =
          eqToHom (congrArg Over.left dy.base) ≫
            Spec.map (CommRingCat.ofHom mphi.ringHom.hom.toRingHom) ≫
            eqToHom (congrArg Over.left dx.base).symm := by
        exact deformationMorphism_arrow_left (q := p ⋙ Over.post B.inclusion) mphi
      have hpsiLeft : B.inclusion.map (p.map mpsi.arrow).left =
          eqToHom (congrArg Over.left dz.base) ≫
            Spec.map (CommRingCat.ofHom mpsi.ringHom.hom.toRingHom) ≫
            eqToHom (congrArg Over.left dx.base).symm := by
        exact deformationMorphism_arrow_left (q := p ⋙ Over.post B.inclusion) mpsi
      have hcomm : s ≫ p.map mphi.arrow = p.map mpsi.arrow := by
        have hc :
            (eqToHom (congrArg Over.left dz.base) ≫
              Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
              eqToHom (congrArg Over.left dy.base).symm) ≫
            (eqToHom (congrArg Over.left dy.base) ≫
              Spec.map (CommRingCat.ofHom mphi.ringHom.hom.toRingHom) ≫
              eqToHom (congrArg Over.left dx.base).symm) =
            eqToHom (congrArg Over.left dz.base) ≫
              Spec.map (CommRingCat.ofHom mpsi.ringHom.hom.toRingHom) ≫
              eqToHom (congrArg Over.left dx.base).symm := by
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [specMap_comp_assoc, hRing]
        apply (Over.post B.inclusion).map_injective
        apply Over.OverMorphism.ext
        exact (congrArg₂ (fun a b => a ≫ b) hsLeft hphiLeft).trans (hc.trans hpsiLeft.symm)
      obtain ⟨χ, ⟨hχmap, hχcomp⟩, hχuniq⟩ :=
        hp.unique_lift mphi.arrow mpsi.arrow s hcomm
      have htriangle : dz.arrow ≫ χ = dy.arrow := by
        apply fibered_hom_ext hp _ _ mphi.arrow
        · have hzbase := deformationObject_arrow_left dz
          have hybase := deformationObject_arrow_left dy
          have hχleft : ((p ⋙ Over.post B.inclusion).map χ).left =
              eqToHom (congrArg Over.left dz.base) ≫
                Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
                eqToHom (congrArg Over.left dy.base).symm := by
            change B.inclusion.map (p.map χ).left = _
            rw [hχmap]
            exact hsLeft
          have hc :
              (eqToHom (congrArg Over.left hx₀) ≫
                Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap dz.algebra)) ≫
                eqToHom (congrArg Over.left dz.base).symm) ≫
              (eqToHom (congrArg Over.left dz.base) ≫
                Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
                eqToHom (congrArg Over.left dy.base).symm) =
              eqToHom (congrArg Over.left hx₀) ≫
                Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap dy.algebra)) ≫
                eqToHom (congrArg Over.left dy.base).symm := by
            simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
            rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, residueMap_comp]
          apply (Over.post B.inclusion).map_injective
          apply Over.OverMorphism.ext
          simpa only [Functor.comp_map, Functor.map_comp, Over.comp_left] using
            (congrArg₂ (fun a b => a ≫ b) hzbase hχleft).trans (hc.trans hybase.symm)
        · rw [Category.assoc, hχcomp]
          exact mpsi.triangle.trans mphi.triangle.symm
      let m : Deformation.Artin.DeformationMorphism iΛ
          (p ⋙ Over.post B.inclusion) x₀ hx₀ dy dz := {
        ringHom := g
        arrow := χ
        triangle := htriangle
        arrow_base := by
          change eqToHom (congrArg Over.left dz.base).symm ≫
            B.inclusion.map (p.map χ).left ≫
            eqToHom (congrArg Over.left dy.base) = _
          rw [hχmap, hsLeft]
          exact eqToHom_conj_cancel (𝒞 := Scheme.{u}) _ _ _ _ _ }
      let l : y' ⟶ z' := (C.morphisms y' z').symm m
      have hl : C.morphisms y' z' l = m := (C.morphisms y' z').apply_symm_apply m
      have hlmap : C.projection.map l = f.unop := by
        rw [construction_projection_map, hl]
        dsimp [m, g]
        simp
      have hlcomp : phi.unop ≫ l = psi.unop := by
        apply (C.morphisms x' z').injective
        apply DeformationMorphism.ext_of_components
        · rw [← C.morphism_projection, ← C.morphism_projection,
            Functor.map_comp, hlmap, hbase]
        · rw [C.reversed_composition, hl]
          exact hχcomp
      refine ⟨l.op, ⟨?_, ?_⟩, ?_⟩
      · exact congrArg Quiver.Hom.op hlmap
      · exact congrArg Quiver.Hom.op hlcomp
      · intro t ht
        apply Quiver.Hom.unop_inj
        change t.unop = l
        apply (C.morphisms y' z').injective
        apply DeformationMorphism.ext_of_components
        · rw [← C.morphism_projection, ← C.morphism_projection, hlmap]
          have htmap := congrArg Quiver.Hom.unop ht.1
          change C.projection.map t.unop = f.unop at htmap
          rw [htmap]
        · rw [hl]
          apply hχuniq
          constructor
          · apply (Over.post B.inclusion).map_injective
            apply Over.OverMorphism.ext
            have htmap := congrArg Quiver.Hom.unop ht.1
            change C.projection.map t.unop = f.unop at htmap
            have htr : (C.morphisms y' z' t.unop).ringHom = g := by
              rw [← C.morphism_projection, htmap]
            change B.inclusion.map (p.map (C.morphisms y' z' t.unop).arrow).left =
              B.inclusion.map s.left
            rw [hsLeft]
            have ha := (C.morphisms y' z' t.unop).arrow_base
            rw [htr] at ha
            exact cancel_eqToHom (congrArg Over.left dz.base)
              (congrArg Over.left dy.base) ha
          · have htcomp := congrArg Quiver.Hom.unop ht.2
            change phi.unop ≫ t.unop = psi.unop at htcomp
            have hc := congrArg (fun t => (C.morphisms x' z' t).arrow) htcomp
            rw [C.reversed_composition] at hc
            exact hc
  · classical
    let K := Deformation.residueFieldObject.{u,u,u} Λ k
    have hKiso : IsIso (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap K))) := by
      dsimp [K]
      rw [residueMap_residueFieldObject]
      have : IsIso (CommRingCat.ofHom (ULift.ringEquiv : ULift.{u} k ≃+* k).toRingHom) :=
        (ULift.ringEquiv : ULift.{u} k ≃+* k).toCommRingCatIso.isIso_hom
      infer_instance
    have harrowIso (d : Deformation.Artin.DeformationObject iΛ
        (p ⋙ Over.post B.inclusion) x₀ hx₀) (hd : d.algebra = K) : IsIso d.arrow := by
      have hr : IsIso (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap d.algebra))) :=
        hd.symm ▸ hKiso
      have he := deformationObject_arrow_left d
      have : IsIso (B.inclusion.map (p.map d.arrow).left) := by
        change IsIso (((p ⋙ Over.post B.inclusion).map d.arrow).left)
        rw [he]
        infer_instance
      have : IsIso (p.map d.arrow).left := isIso_of_reflects_iso _ B.inclusion
      have : IsIso ((Over.forget _).map (p.map d.arrow)) := ‹IsIso (p.map d.arrow).left›
      have : IsIso (p.map d.arrow) := isIso_of_reflects_iso _ (Over.forget _)
      exact fibered_isIso hp d.arrow
    apply (equiv_punit_iff_unique (C.projection.Fiber K)).mpr
    constructor
    · let hk := spec_k_lt_cutoff B hS iΛ p x₀ hx₀
      let hK := spec_artinian_size_lt B K hk
      let r := siteResidueMap B hS iΛ K hK hk
      have hrleft : IsIso (B.inclusion.map r.left) := by
        have he : B.inclusion.map r.left =
            Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap K)) :=
          congrArg Over.Hom.left (siteResidueMap_post B hS iΛ K hK hk)
        rw [he]
        exact hKiso
      have : IsIso r.left := isIso_of_reflects_iso _ B.inclusion
      have : IsIso ((Over.forget _).map r) := ‹IsIso r.left›
      have : IsIso r := isIso_of_reflects_iso _ (Over.forget _)
      have hx0site := specialPoint_baseSite B hS iΛ p x₀ hx₀
      obtain ⟨y, ψ, hψ⟩ := hp.exists_lift (inv r) x₀ hx0site
      have hy := IsHomLift.domain_eq p (inv r) ψ
      have hψmap : p.map ψ = eqToHom hy ≫ inv r ≫ eqToHom hx0site.symm :=
        IsHomLift.fac' p (inv r) ψ
      have : IsIso (p.map ψ) := by rw [hψmap]; infer_instance
      have : IsIso ψ := fibered_isIso hp ψ
      have hχmap : p.map (inv ψ) = eqToHom hx0site ≫ r ≫ eqToHom hy.symm := by
        simp only [Functor.map_inv, hψmap, IsIso.inv_comp, inv_eqToHom, IsIso.inv_inv,
          Category.assoc]
      let d := deformationObjectOfLift B hS iΛ p x₀ hx₀ K hK (inv ψ) hy hχmap
      obtain ⟨a, ha⟩ := C.objects.surjective d
      exact ⟨⟨a, (C.object_projection a).trans
        (congrArg Deformation.Artin.DeformationObject.algebra ha)⟩⟩
    · intro a b
      let da := C.objects a.val
      let db := C.objects b.val
      have ha : da.algebra = K := (C.object_projection a.val).symm.trans a.property
      have hb : db.algebra = K := (C.object_projection b.val).symm.trans b.property
      have : IsIso db.arrow := harrowIso db hb
      let g : da.algebra ⟶ db.algebra := eqToHom (ha.trans hb.symm)
      let m := deformationMorphismOfIsIso da db g
      let l := (C.morphisms a.val b.val).symm m
      have hl : C.morphisms a.val b.val l = m := (C.morphisms a.val b.val).apply_symm_apply m
      have hlmap : C.projection.map l = eqToHom (a.property.trans b.property.symm) := by
        rw [construction_projection_map, hl]
        dsimp [m, deformationMorphismOfIsIso, g]
        simp
      have hlift : C.projection.IsHomLift (𝟙 K) l := by
        apply IsHomLift.of_fac _ _ _ a.property b.property
        rw [hlmap]
        simp
      refine ⟨{ default := ⟨l, hlift⟩, uniq := ?_ }⟩
      intro t
      apply Subtype.ext
      apply (C.morphisms a.val b.val).injective
      apply DeformationMorphism.ext_of_components
      · rw [← C.morphism_projection, ← C.morphism_projection, hlmap]
        have := t.property
        have ht := IsHomLift.fac' C.projection (𝟙 K) t.val
        rw [ht]
        simp
      · rw [hl]
        apply (cancel_epi db.arrow).mp
        exact (C.morphisms a.val b.val t.val).triangle.trans m.triangle.symm

end Deformation.Artin
