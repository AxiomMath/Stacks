module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleCover
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedExactness
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleLimits
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.LocallyConstantTrivialization
import all StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleLimits

/-!
# Finite coproducts in the site of affine ind-étale objects

Let `S` be a scheme and `S_app` the category of affine objects of the small pro-étale site of `S`
whose ring of global sections is ind-étale over that of `S` (Stacks 098X), with the topology
induced from the small pro-étale site. A finite disjoint union of such objects is again one, and
it is their coproduct in `S_app`. Every sheaf of sets on `S_app` takes such a coproduct to a
product.

At an object `W` whose ring of global sections is w-contractible, the total map `∐ Tₖ ⟶ W` of a
jointly surjective finite family of morphisms `Tₖ ⟶ W` of `S_app` has a section.

## Main definitions

* `AlgebraicGeometry.ProEtale.AppProetale.sigmaObj`: the disjoint union of a finite family of
  objects of `S_app`, with its injections `sigmaι` and the induced maps `sigmaDesc`.

## Main results

* `AlgebraicGeometry.ProEtale.AppProetale.isColimitSigmaCofan`: the disjoint union is the
  coproduct.
* `AlgebraicGeometry.ProEtale.AppProetale.bijective_map_cofan_inj_of_isSheaf`: a sheaf of sets on
  `S_app` takes a finite coproduct to a product.
* `AlgebraicGeometry.ProEtale.AppProetale.exists_comp_sigmaDesc_eq_id`: at an object with
  w-contractible ring of global sections, the total map of a jointly surjective finite family
  has a section.

## References

* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 0981](https://stacks.math.columbia.edu/tag/0981)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t u

namespace AlgebraicGeometry.ProEtale.AppProetale

variable {S : Scheme.{u}}

/-- Two morphisms of `S_app` are equal as soon as their underlying morphisms of schemes are. -/
theorem hom_ext {V W : AppProetale S} {a b : V ⟶ W} (h : a.hom.left = b.hom.left) : a = b :=
  ObjectProperty.hom_ext _ (MorphismProperty.Over.Hom.ext h)

/-- A sieve of `S_app` is covering if its pushforward to the pro-étale site is. -/
private theorem mem_inducedTopology_of_functorPushforward_mem [IsAffine S] {Y : AppProetale S}
    {R : Sieve Y} (h : R.functorPushforward (inclusion S) ∈
      Scheme.ProEt.topology S ((inclusion S).obj Y)) :
    R ∈ (inclusion S).inducedTopology (Scheme.ProEt.topology S) Y :=
  have := appInclusion_isDenseSubsite S (hasAppCover S)
  ((inclusion S).functorPushforward_mem_iff _ (Scheme.ProEt.topology S)).mp h

section Sigma

variable {ι : Type u} [Finite ι] (T : ι → AppProetale S)

/-- The disjoint union of the underlying schemes of a finite family of objects of `S_app` is
ind-étale over `S` on global sections. -/
theorem indEtale_appTop_sigmaDesc :
    ObjectProperty.ind.{u} (fun D : Under Γ(S, ⊤) ↦ D.hom.hom.Etale)
      (Under.mk (Sigma.desc fun k ↦ (T k).obj.hom).appTop) :=
  ProEtale.indEtale_appTop_sigmaDesc _ _ fun k ↦ (T k).property.2

/-- The disjoint union of a finite family of affine ind-étale objects of `S`. -/
def sigmaObj : AppProetale S where
  obj := @Scheme.ProEt.mk S (∐ fun k ↦ (T k).obj.left) (Sigma.desc fun k ↦ (T k).obj.hom)
    (IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) fun k ↦ (T k).obj.prop)
  property := ⟨by
      have (k : ι) : IsAffine (T k).obj.left := (T k).property.1
      exact show IsAffine (∐ fun k ↦ (T k).obj.left) from inferInstance,
    indEtale_appTop_sigmaDesc T⟩

/-- The underlying scheme of the disjoint union is the disjoint union of the underlying
schemes. -/
theorem sigmaObj_left : (sigmaObj T).obj.left = ∐ fun k ↦ (T k).obj.left := rfl

/-- The coproduct injections of the disjoint union. -/
def sigmaι (k : ι) : T k ⟶ sigmaObj T :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (Sigma.ι (fun k ↦ (T k).obj.left) k)
    (Sigma.ι_desc _ k))

/-- The underlying morphism of schemes of the `k`-th injection is the `k`-th coproduct
injection. -/
@[simp]
theorem sigmaι_hom_left (k : ι) :
    (sigmaι T k).hom.left = Sigma.ι (fun k ↦ (T k).obj.left) k := rfl

/-- The morphism out of the disjoint union induced by a family of morphisms. -/
def sigmaDesc {W : AppProetale S} (g : ∀ k, T k ⟶ W) : sigmaObj T ⟶ W :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (Sigma.desc fun k ↦ (g k).hom.left)
    (Sigma.hom_ext _ _ fun k ↦ (Sigma.ι_desc_assoc _ _ _).trans
      ((MorphismProperty.Over.w (g k).hom).trans
        (Sigma.ι_desc (fun k ↦ (T k).obj.hom) k).symm)))

/-- The underlying morphism of schemes of `sigmaDesc T g` is the morphism out of the coproduct
induced by the underlying morphisms of the `g k`. -/
@[simp]
theorem sigmaDesc_hom_left {W : AppProetale S} (g : ∀ k, T k ⟶ W) :
    (sigmaDesc T g).hom.left = Sigma.desc fun k ↦ (g k).hom.left := rfl

/-- The `k`-th injection followed by `sigmaDesc T g` is `g k`. -/
@[reassoc (attr := simp)]
theorem sigmaι_sigmaDesc {W : AppProetale S} (g : ∀ k, T k ⟶ W) (k : ι) :
    sigmaι T k ≫ sigmaDesc T g = g k :=
  hom_ext (Sigma.ι_desc _ k)

/-- The disjoint union as a cofan. -/
abbrev sigmaCofan : Cofan T := Cofan.mk (sigmaObj T) (sigmaι T)

/-- **The disjoint union is the coproduct in `S_app`.** -/
def isColimitSigmaCofan : IsColimit (sigmaCofan T) :=
  mkCofanColimit _ (fun s ↦ sigmaDesc T s.inj) (fun s k ↦ sigmaι_sigmaDesc T s.inj k)
    (fun s m hm ↦ hom_ext (Sigma.hom_ext _ _ fun k ↦ by
      rw [sigmaDesc_hom_left, Sigma.ι_desc]
      exact congrArg (fun f ↦ f.hom.left) (hm k)))

/-- The coproduct injections of a finite disjoint union generate a covering sieve. -/
theorem sieve_ofArrows_sigmaι_mem [IsAffine S] :
    Sieve.ofArrows T (sigmaι T) ∈
      (inclusion S).inducedTopology (Scheme.ProEt.topology S) (sigmaObj T) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine mem_inducedTopology_of_functorPushforward_mem ?_
  rw [Sieve.functorPushforward_ofArrows]
  have : IsAffine (sigmaObj T).obj.left := (sigmaObj T).property.1
  refine Scheme.ProEt.ofArrows_mem_topology_of_isAffine (fun k ↦ (T k).obj)
    (fun k ↦ (sigmaι T k).hom) n e.symm (fun _ ↦ ⊤) (fun m ↦ ?_) ?_
  · have := (T (e.symm m)).property.1
    rw [TopologicalSpace.Opens.coe_top]
    exact isCompact_univ
  · refine (e.symm.surjective.iUnion_comp
      (fun k ↦ (sigmaι T k).hom.left '' ((⊤ : (T k).obj.left.Opens) : Set (T k).obj.left))).trans
      (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨k, y, rfl⟩ := (sigmaOpenCover fun k ↦ (T k).obj.left).exists_eq x
    exact Set.mem_iUnion.mpr ⟨k, y, trivial, rfl⟩

end Sigma

/-- An object of `S_app` with empty underlying scheme is covered by the empty sieve. -/
theorem bot_mem_of_isEmpty [IsAffine S] {Y : AppProetale S} (hY : IsEmpty Y.obj.left) :
    (⊥ : Sieve Y) ∈ (inclusion S).inducedTopology (Scheme.ProEt.topology S) Y := by
  refine mem_inducedTopology_of_functorPushforward_mem ?_
  rw [Sieve.functorPushforward_bot]
  exact Scheme.ProEt.bot_mem_topology_of_isEmpty Y.obj hY

/-- **A sheaf of sets on `S_app` takes a finite coproduct to a product.** -/
theorem bijective_map_cofan_inj_of_isSheaf [IsAffine S] {ι : Type u} [Finite ι]
    {T : ι → AppProetale S} (P : (AppProetale S)ᵒᵖ ⥤ Type t)
    (hP : Presieve.IsSheaf ((inclusion S).inducedTopology (Scheme.ProEt.topology S)) P)
    {c : Cofan T} (hc : IsColimit c) :
    Function.Bijective (fun x : P.obj (op c.pt) ↦ fun k ↦ P.map (c.inj k).op x) := by
  classical
  let e : c.pt ≅ sigmaObj T := hc.coconePointUniqueUpToIso (isColimitSigmaCofan T)
  have he (k : ι) : c.inj k ≫ e.hom = sigmaι T k :=
    hc.comp_coconePointUniqueUpToIso_hom (isColimitSigmaCofan T) ⟨k⟩
  suffices hσ : Function.Bijective
      (fun x : P.obj (op (sigmaObj T)) ↦ fun k ↦ P.map (sigmaι T k).op x) by
    have hcomp : (fun x : P.obj (op c.pt) ↦ fun k ↦ P.map (c.inj k).op x) =
        (fun x : P.obj (op (sigmaObj T)) ↦ fun k ↦ P.map (sigmaι T k).op x) ∘
          P.map e.inv.op := by
      funext x k
      simp only [Function.comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp]
      congr 2
      rw [← he k, Category.assoc, e.hom_inv_id, Category.comp_id]
    rw [hcomp]
    exact hσ.comp ((isIso_iff_bijective _).mp (inferInstance : IsIso (P.map e.inv.op)))
  have hsh : Presieve.IsSheafFor P (Presieve.ofArrows T (sigmaι T)) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hP _ (sieve_ofArrows_sigmaι_mem T))
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  have hcompat (x : ∀ k, P.obj (op (T k))) : Presieve.Arrows.Compatible P (sigmaι T) x := by
    intro i j Y gi gj h
    have h' := congrArg (fun f ↦ f.hom.left) h
    by_cases hij : i = j
    · subst hij
      rw [hom_ext ((cancel_mono (Sigma.ι (fun k ↦ (T k).obj.left) i)).mp h')]
    · have hY : IsEmpty Y.obj.left := ⟨fun y ↦ by
        have hy := congrArg (fun f ↦ f y) h'
        dsimp only at hy
        have hi : (gi ≫ sigmaι T i).hom.left y ∈
            (Sigma.ι (fun k ↦ (T k).obj.left) i).opensRange := ⟨gi.hom.left y, rfl⟩
        have hj : (gi ≫ sigmaι T i).hom.left y ∈
            (Sigma.ι (fun k ↦ (T k).obj.left) j).opensRange := hy ▸ ⟨gj.hom.left y, rfl⟩
        exact (disjoint_opensRange_sigmaι (fun k ↦ (T k).obj.left) i j hij).le_bot ⟨hi, hj⟩⟩
      exact (hP _ (bot_mem_of_isEmpty hY)).isSeparatedFor.ext fun _ _ h ↦ h.elim
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨t, -, ht⟩ := hsh (fun k ↦ P.map (sigmaι T k).op x) (hcompat _)
    exact (ht x fun k ↦ rfl).trans (ht y fun k ↦ (congrFun hxy k).symm).symm
  · obtain ⟨t, ht, -⟩ := hsh z (hcompat z)
    exact ⟨t, funext ht⟩

/-- **A surjection onto an affine scheme with w-contractible global sections splits.** Let
`d : X ⟶ Y` be a surjective weakly étale morphism of affine schemes, with `Γ(Y, ⊤)` w-contractible.
Then `d` has a section. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_comp_eq_id_of_isWContractible {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (d : X ⟶ Y) [WeaklyEtale d] [Surjective d]
    (hY : ProetaleWContractible.IsWContractible.{u, u} Γ(Y, ⊤)) : ∃ σ : Y ⟶ X, σ ≫ d = 𝟙 Y := by
  let r := d.appTop
  have hSpec (P : MorphismProperty Scheme) [P.RespectsIso] (h : P d) : P (Spec.map r) :=
    (P.arrow_mk_iso_iff (arrowIsoSpecΓOfIsAffine d)).mp h
  have hwe' : WeaklyEtale (Spec.map r) := hSpec @WeaklyEtale inferInstance
  have hsurj' : Surjective (Spec.map r) := hSpec @Surjective inferInstance
  have hff : r.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff r).mp
    ⟨inferInstance, hsurj'⟩
  algebraize [r.hom]
  have hweA := (Algebra.weaklyEtale_iff _ _).mp ((weaklyEtale_specMap_iff r).mp hwe')
  obtain ⟨ρ⟩ := hY Γ(X, ⊤) hweA hff
  have hρ : r ≫ CommRingCat.ofHom ρ.toRingHom = 𝟙 _ := by
    ext a
    exact ρ.commutes a
  refine ⟨Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ X.isoSpec.inv, ?_⟩
  rw [Category.assoc, Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, hρ,
    Spec.map_id, Category.id_comp, Iso.hom_inv_id]

/-- **A surjection onto an object with w-contractible global sections splits.** -/
theorem exists_comp_eq_id_of_surjective {V W : AppProetale S}
    (hW : ProetaleWContractible.IsWContractible.{u, u} Γ(W.obj.left, ⊤)) (d : V ⟶ W)
    (hd : Function.Surjective d.hom.left) : ∃ σ : W ⟶ V, σ ≫ d = 𝟙 W := by
  have : IsAffine V.obj.left := V.property.1
  have : IsAffine W.obj.left := W.property.1
  have : WeaklyEtale d.hom.left := by
    have hk : WeaklyEtale (d.hom.left ≫ W.obj.hom) := by
      rw [MorphismProperty.Over.w d.hom]
      exact V.obj.prop
    exact MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale) d.hom.left
      W.obj.hom W.obj.prop hk
  have : Surjective d.hom.left := ⟨hd⟩
  obtain ⟨σ, hσ⟩ := Scheme.exists_comp_eq_id_of_isWContractible d.hom.left hW
  refine ⟨ObjectProperty.homMk (MorphismProperty.Over.homMk σ ?_), hom_ext hσ⟩
  calc σ ≫ V.obj.hom = σ ≫ d.hom.left ≫ W.obj.hom := by rw [MorphismProperty.Over.w d.hom]
    _ = W.obj.hom := by rw [← Category.assoc, hσ, Category.id_comp]

/-- **At an object with w-contractible global sections, a jointly surjective finite family
splits through its disjoint union.** -/
theorem exists_comp_sigmaDesc_eq_id {ι : Type u} [Finite ι] {T : ι → AppProetale S}
    {W : AppProetale S} (hW : ProetaleWContractible.IsWContractible.{u, u} Γ(W.obj.left, ⊤))
    (f : ∀ k, T k ⟶ W) (hf : ∀ x : W.obj.left, ∃ k y, (f k).hom.left y = x) :
    ∃ σ : W ⟶ sigmaObj T, σ ≫ sigmaDesc T f = 𝟙 W := by
  refine exists_comp_eq_id_of_surjective hW _ fun x ↦ ?_
  obtain ⟨k, y, rfl⟩ := hf x
  exact ⟨Sigma.ι (fun k ↦ (T k).obj.left) k y,
    congrArg (fun g ↦ g y) (Sigma.ι_desc (fun k ↦ (f k).hom.left) k)⟩

end AlgebraicGeometry.ProEtale.AppProetale

end
