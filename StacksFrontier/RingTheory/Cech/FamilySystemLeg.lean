module

public import StacksFrontier.RingTheory.Cech.FamilySystemPresheaf
public import StacksFrontier.RingTheory.Cech.PresheafComplex
public import StacksFrontier.RingTheory.Cech.SemilinearIsBaseChange

/-!
# The leg of a distinguished family

Let `R` be a presheaf of commutative rings on a category `C` and let `F` be a family system on it
(`Stacks.CechFamilySystem.FamilySystem`). Over each object `V` the presheaf of Čech complexes of
`F` is the filtered colimit of the Čech complexes of the product families of the finite sets of
distinguished families over `V`. This file builds the leg of that colimit at a single
distinguished family `x`,

`Stacks.CechFamilySystem.legAt n x : C^n(x; R(V)) ⟶ colim_S C^n(fam S; R(V))`,

and assembles these legs, for a family `f₁, …, f_r` given over every object of a category `D`
mapping to `C` by a functor `G`, compatible with restriction and distinguished over every object,
into a map of complexes of presheaves of modules on `D`

`Stacks.CechFamilySystem.legNat G F f hf hmem :
  K(R(G -), f) ⟶ G^* (Stacks.CechFamilySystem.cechComplexPresheafNat F)`

from the sectionwise Čech complex of that one family into the restriction along `G` of the
presheaf of Čech complexes of the family system. The case of interest is `G = Over.forget U` for
an object `U` of a site: a family generating a sheaf of ideals on the slice at `U` is given over
the objects of the slice, not over those of the site.

Over an object `V` the leg is the leg of the colimit at the singleton index `{x}`, precomposed with
the reindexing that identifies the Čech complex of `x` with the Čech complex of the product family
of that singleton — the product over a one-element set of families, which is the family itself up
to the bijection `Stacks.CechFamilySystem.singleIdx` of index types.

**Why the restriction maps match.** The leg at `x` lands at the index `{x}`, the leg at `x|_W` at
the index `{x|_W}`, and the restriction map of the colimit presheaf carries the stage `{x}` to the
stage `GenSet.map a {x} = {x|_W}`. The two legs therefore differ by a transition of the diagram
along an equality of indices, and the whole of the naturality is the combinatorial identity
`Stacks.CechFamilySystem.singleIdx_comp_idxLe`: the two index maps it compares both evaluate a
choice for `GenSet.map a {x}` at its only member `x|_W`. The ring-theoretic half — that the
semilinear change of rings of the sectionwise complex and the `Cech.genRingTerm` calculus of the
colimit presheaf are the same map — is `Stacks.CechSemilinear.genTerm_comp_termMap` of
`SemilinearIsBaseChange.lean`.

## Main definitions

* `Stacks.CechFamilySystem.singleIdx`: the index bijection of a singleton index.
* `Stacks.CechFamilySystem.singleLeg`: the reindexing `Č(x) ⟶ Č(fam {x})`.
* `Stacks.CechFamilySystem.legAt`: **the leg at one distinguished family.**
* `Stacks.CechFamilySystem.legTerm` and `Stacks.CechFamilySystem.legNat`: **the comparison of
  complexes of presheaves of modules** along a functor `G : D ⥤ C`.

## Main results

* `Stacks.CechFamilySystem.singleLeg_naturality`: the reindexing commutes with transport, at the
  level of the stages of the diagram.
* `Stacks.CechFamilySystem.legAt_naturality` and `Stacks.CechFamilySystem.legAt_mk_naturality`:
  the leg commutes with restriction.
* `Stacks.CechFamilySystem.legAt_comm`: the leg commutes with the differentials.
* `Stacks.CechFamilySystem.legAt_comp_augDesc` and
  `Stacks.CechFamilySystem.legTerm_zero_comp_cechAugZero`: **the leg is a map over `R`** in degree
  zero.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CechFamilySystem

open FamilySystem

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-! ### The index bijection of a singleton index -/

section Single

variable {F : FamilySystem R}

/-- The two reindexings of a singleton index, read backwards: the choice of a factor out of the
product family of `{x}` is an index into `x` itself. -/
def singleIdx {V : Cᵒᵖ} (x : F.Gen V) : Fin (famCard (single x)) → Fin x.arity :=
  fun k => idxSingleEquiv x ((idxEquiv (single x)).symm k)

/-- The index bijection of `{x}` evaluates a choice of a factor at the only member of `{x}`. -/
theorem singleIdx_apply {V : Cᵒᵖ} (x : F.Gen V) (k : Fin (famCard (single x))) :
    singleIdx x k = ((idxEquiv (single x)).symm k) default := rfl

/-- **The product family of a singleton index is the family itself**, read through
`Stacks.CechFamilySystem.singleIdx`. -/
theorem fam_single_apply {V : Cᵒᵖ} (x : F.Gen V) (k : Fin (famCard (single x))) :
    fam (single x) k = x.elts (singleIdx x k) :=
  (fam_apply (single x) k).trans (famFun_single x _)

/-- Some power of each value of the product family of `{x}` is divisible by the corresponding
member of `x`; the first power is, since the two are equal. -/
theorem exists_dvd_fam_single {V : Cᵒᵖ} (x : F.Gen V) (k : Fin (famCard (single x))) :
    ∃ n : ℕ, x.elts (singleIdx x k) ∣ fam (single x) k ^ n :=
  ⟨1, by rw [pow_one, fam_single_apply]⟩

/-- **The reindexing `Č(x) ⟶ Č(fam {x})`** of the Čech complex of a distinguished family onto the
Čech complex of the product family of its singleton index. -/
def singleLeg {V : Cᵒᵖ} (x : F.Gen V) :
    Cech.cechComplex x.elts (R.obj V) ⟶ Cech.cechComplex (fam (single x)) (R.obj V) :=
  Cech.cechGenMap x.elts (fam (single x)) (singleIdx x) (exists_dvd_fam_single x) (R.obj V)

/-- The degree-`n` component of `Stacks.CechFamilySystem.singleLeg x` is the map `Cech.genTerm`
along `Stacks.CechFamilySystem.singleIdx x`. -/
theorem singleLeg_f {V : Cᵒᵖ} (x : F.Gen V) (n : ℕ) :
    ((singleLeg x).f n).hom =
      Cech.genTerm x.elts (fam (single x)) (singleIdx x) (exists_dvd_fam_single x)
        (R.obj V) n :=
  rfl

/-! ### The two index maps, read backwards through the reindexings by `Fin` -/

/-- The restriction index map `idxMap a S`, read through the reindexings by `Fin`, is
`idxMapFun a S`. -/
theorem symm_idxMap {V W : Cᵒᵖ} (a : V ⟶ W) (S : F.GenSet V)
    (k : Fin (famCard (GenSet.map a S))) :
    (idxEquiv S).symm (idxMap a S k) = idxMapFun a S ((idxEquiv (GenSet.map a S)).symm k) := by
  rw [idxMap, Equiv.symm_apply_apply]

/-- The inclusion index map `idxLe h`, read through the reindexings by `Fin`, is `idxLeFun h`. -/
theorem symm_idxLe {V : Cᵒᵖ} {S T : F.GenSet V} (h : S ≤ T) (k : Fin (famCard T)) :
    (idxEquiv S).symm (idxLe h k) = idxLeFun h ((idxEquiv T).symm k) := by
  rw [idxLe, Equiv.symm_apply_apply]

end Single

/-! ### The leg at one distinguished family -/

section Local

variable {F : FamilySystem R}

/-- **The leg of the colimit at one distinguished family**, degreewise: the reindexing onto the
product family of its singleton index, followed by the leg of the colimit at that index. -/
def legAt (n : ℕ) {V : Cᵒᵖ} (x : F.Gen V) :
    (Cech.cechComplex x.elts (R.obj V)).X n ⟶
      (colimit (cechTermDiagram F V n) : ModuleCat.{u} (R.obj V)) :=
  (singleLeg x).f n ≫ colimit.ι (cechTermDiagram F V n) (single x)

/-- The leg at `x` applied to a cochain is the leg of the colimit at `{x}` applied to its
reindexing along `Stacks.CechFamilySystem.singleIdx x`. -/
theorem legAt_hom_apply (n : ℕ) {V : Cᵒᵖ} (x : F.Gen V) (z : Cech.cechTerm x.elts (R.obj V) n) :
    (legAt n x).hom z =
      (colimit.ι (cechTermDiagram F V n) (single x)).hom
        (Cech.genTerm x.elts (fam (single x)) (singleIdx x) (exists_dvd_fam_single x)
          (R.obj V) n z) :=
  rfl

/-- The divisibility of a family against the product family of the restriction of its singleton
index. -/
theorem exists_dvd_fam_single_idxMap {V W : Cᵒᵖ} (a : V ⟶ W) (x : F.Gen V)
    (k : Fin (famCard (GenSet.map a (single x)))) :
    ∃ m : ℕ, (R.map a).hom (x.elts (singleIdx x (idxMap a (single x) k))) ∣
      fam (GenSet.map a (single x)) k ^ m := by
  obtain ⟨m, hm⟩ := exists_dvd_map_fam a (single x) k
  rw [fam_single_apply] at hm
  exact ⟨m, hm⟩

/-- The two index maps out of the product family of the restriction of a singleton index agree:
the restriction of the index bijection of `x`, and the index bijection of `x|_W` read through the
equality `{x|_W} = GenSet.map a {x}`. -/
theorem singleIdx_comp_idxLe {V W : Cᵒᵖ} (a : V ⟶ W) (x : F.Gen V) :
    singleIdx (Gen.map a x) ∘ idxLe (map_single a x).ge =
      singleIdx x ∘ idxMap a (single x) := by
  funext k
  refine Fin.val_injective ?_
  rw [Function.comp_apply, Function.comp_apply, singleIdx_apply, singleIdx_apply, symm_idxMap,
    symm_idxLe]
  rfl

/-- **The naturality of the reindexing onto a singleton index**, at the level of the stages of
the diagram: transporting the reindexed cochain of `x` along `a` gives the reindexed restricted
cochain of `x|_W`, read at the stage `GenSet.map a {x} = {x|_W}`.

Both sides are a single `Cech.genRingTerm` along `R.map a`, by
`Stacks.CechSemilinear.genTerm_comp_termMap`, `Cech.genTerm_comp_genRingTerm` and
`Cech.genRingTerm_comp_genTerm`, and the two index maps agree by
`Stacks.CechFamilySystem.singleIdx_comp_idxLe`. -/
theorem singleLeg_naturality (n : ℕ) {V W : Cᵒᵖ} (a : V ⟶ W) (x : F.Gen V)
    (z : Cech.cechTerm x.elts (R.obj V) n) :
    (((cechDiagram F W).map (homOfLE (map_single a x).ge)).f n).hom
        (((singleLeg (Gen.map a x)).f n).hom
          (CechSemilinear.termMap (R.map a).hom x.elts (Gen.map a x).elts (fun _ => rfl) n z)) =
      ((cechTransport F a (single x)).f n).hom (((singleLeg x).f n).hom z) := by
  have hL : (((cechDiagram F W).map (homOfLE (map_single a x).ge)).f n).hom
        (((singleLeg (Gen.map a x)).f n).hom
          (CechSemilinear.termMap (R.map a).hom x.elts (Gen.map a x).elts (fun _ => rfl) n z)) =
      Cech.genRingTerm (R.map a).hom x.elts (fam (GenSet.map a (single x)))
        (singleIdx (Gen.map a x) ∘ idxLe (map_single a x).ge)
        (fun k => (exists_dvd_fam_single (Gen.map a x) (idxLe (map_single a x).ge k)).elim
          fun m hm => ⟨m, hm.trans (pow_dvd_pow_of_dvd
            (fam_dvd_of_le (map_single a x).ge k) m)⟩) n z := by
    refine (congrArg (fun y => (((cechDiagram F W).map
        (homOfLE (map_single a x).ge)).f n).hom y)
      (CechSemilinear.genTerm_comp_termMap (R.map a).hom x.elts (Gen.map a x).elts
        (fun _ => rfl) rfl (fam (single (Gen.map a x))) (singleIdx (Gen.map a x))
        (exists_dvd_fam_single (Gen.map a x)) (exists_dvd_fam_single (Gen.map a x)) n z)).trans
      ?_
    exact LinearMap.congr_fun (Cech.genTerm_comp_genRingTerm (R.map a).hom x.elts
      (fam (single (Gen.map a x))) (fam (GenSet.map a (single x))) (singleIdx (Gen.map a x))
      (exists_dvd_fam_single (Gen.map a x)) (idxLe (map_single a x).ge)
      (exists_dvd_fam_of_le (map_single a x).ge) _ _ rfl n) z
  have hR : ((cechTransport F a (single x)).f n).hom (((singleLeg x).f n).hom z) =
      Cech.genRingTerm (R.map a).hom x.elts (fam (GenSet.map a (single x)))
        (singleIdx x ∘ idxMap a (single x)) (exists_dvd_fam_single_idxMap a x) n z :=
    LinearMap.congr_fun (Cech.genRingTerm_comp_genTerm (R.map a).hom x.elts
      (fam (single x)) (fam (GenSet.map a (single x))) (singleIdx x) (exists_dvd_fam_single x)
      (idxMap a (single x)) (exists_dvd_map_fam a (single x)) _ _ rfl n) z
  have hcongr : ∀ (γ₁ γ₂ : Fin (famCard (GenSet.map a (single x))) → Fin x.arity)
      (h₁ : ∀ k, ∃ m : ℕ, (R.map a).hom (x.elts (γ₁ k)) ∣ fam (GenSet.map a (single x)) k ^ m)
      (h₂ : ∀ k, ∃ m : ℕ, (R.map a).hom (x.elts (γ₂ k)) ∣ fam (GenSet.map a (single x)) k ^ m),
      γ₁ = γ₂ →
        Cech.genRingTerm (R.map a).hom x.elts (fam (GenSet.map a (single x))) γ₁ h₁ n z =
          Cech.genRingTerm (R.map a).hom x.elts (fam (GenSet.map a (single x))) γ₂ h₂ n z := by
    rintro γ₁ γ₂ h₁ h₂ rfl
    rfl
  exact hL.trans ((hcongr _ _ _ _ (singleIdx_comp_idxLe a x)).trans hR.symm)

/-- **The naturality of the leg**, on elements: the leg at the restriction `x|_W` applied to the
restriction of a cochain is the restriction of the leg at `x` applied to it.

The two sides are legs of the colimit at the indices `{x|_W}` and `GenSet.map a {x}`, which are
equal (`Stacks.CechFamilySystem.FamilySystem.map_single`), so they differ by a transition of the
diagram, and the stage-level identity is `Stacks.CechFamilySystem.singleLeg_naturality`. -/
theorem legAt_naturality (n : ℕ) {V W : Cᵒᵖ} (a : V ⟶ W) (x : F.Gen V)
    (z : Cech.cechTerm x.elts (R.obj V) n) :
    (legAt n (Gen.map a x)).hom
        (CechSemilinear.termMap (R.map a).hom x.elts (Gen.map a x).elts (fun _ => rfl) n z) =
      (transportDesc F a n).hom ((legAt n x).hom z) :=
  (colimit_ι_apply_of_le F W n (homOfLE (map_single a x).ge) _).symm.trans
    ((congrArg (fun y => (colimit.ι (cechTermDiagram F W n) (GenSet.map a (single x))).hom y)
      (singleLeg_naturality n a x z)).trans
      (transportDesc_ι_apply F a n (single x) _).symm)

/-- **The naturality of the leg, for two families of the same arity related by the restriction
map.** -/
theorem legAt_mk_naturality (n : ℕ) {V W : Cᵒᵖ} (a : V ⟶ W) {r : ℕ} (f : Fin r → R.obj V)
    (f' : Fin r → R.obj W) (hf : ∀ i, (R.map a).hom (f i) = f' i) (mf : F.Mem f)
    (mf' : F.Mem f') (z : Cech.cechTerm f (R.obj V) n) :
    (legAt n (⟨r, f', mf'⟩ : F.Gen W)).hom (CechSemilinear.termMap (R.map a).hom f f' hf n z) =
      (transportDesc F a n).hom ((legAt n (⟨r, f, mf⟩ : F.Gen V)).hom z) := by
  obtain rfl : f' = fun i => (R.map a).hom (f i) := funext fun i => (hf i).symm
  exact legAt_naturality n a ⟨r, f, mf⟩ z

/-- **The stage-level naturality of the reindexing, for two families of the same arity related by
the restriction map.** -/
theorem singleLeg_mk_naturality (n : ℕ) {V W : Cᵒᵖ} (a : V ⟶ W) {r : ℕ} (f : Fin r → R.obj V)
    (f' : Fin r → R.obj W) (hf : ∀ i, (R.map a).hom (f i) = f' i) (mf : F.Mem f)
    (mf' : F.Mem f') (h : single (⟨r, f', mf'⟩ : F.Gen W) ≤ GenSet.map a (single ⟨r, f, mf⟩))
    (z : Cech.cechTerm f (R.obj V) n) :
    (((cechDiagram F W).map (homOfLE h)).f n).hom
        (((singleLeg (⟨r, f', mf'⟩ : F.Gen W)).f n).hom
          (CechSemilinear.termMap (R.map a).hom f f' hf n z)) =
      ((cechTransport F a (single ⟨r, f, mf⟩)).f n).hom
        (((singleLeg (⟨r, f, mf⟩ : F.Gen V)).f n).hom z) := by
  obtain rfl : f' = fun i => (R.map a).hom (f i) := funext fun i => (hf i).symm
  exact singleLeg_naturality n a ⟨r, f, mf⟩ z

/-- The differential of the diagram, read as the Čech differential of the product family. -/
theorem cechDiffTerm_hom (V : Cᵒᵖ) (n : ℕ) (S : F.GenSet V) :
    (cechDiffTerm F V n S).hom = Cech.cechD (fam S) (R.obj V) n :=
  congrArg ModuleCat.Hom.hom
    (CochainComplex.of_d (fun p => ModuleCat.of (R.obj V) (Cech.cechTerm (fam S) (R.obj V) p))
      (fun p => ModuleCat.ofHom (Cech.cechD (fam S) (R.obj V) p)) n)

/-- **The leg commutes with the Čech differentials.** -/
theorem legAt_comm (n : ℕ) {V : Cᵒᵖ} (x : F.Gen V) (z : Cech.cechTerm x.elts (R.obj V) n) :
    (legAt (n + 1) x).hom (Cech.cechD x.elts (R.obj V) n z) =
      (diffDesc F V n).hom ((legAt n x).hom z) := by
  refine Eq.trans (congrArg
    (fun y => (colimit.ι (cechTermDiagram F V (n + 1)) (single x)).hom y)
    (Cech.genTerm_comm x.elts (fam (single x)) (singleIdx x)
      (exists_dvd_fam_single x) (R.obj V) n z)) ?_
  refine Eq.trans (congrArg
    (fun m : Cech.cechTerm (fam (single x)) (R.obj V) n →
        Cech.cechTerm (fam (single x)) (R.obj V) (n + 1) =>
      (colimit.ι (cechTermDiagram F V (n + 1)) (single x)).hom
        (m (Cech.genTerm x.elts (fam (single x)) (singleIdx x)
          (exists_dvd_fam_single x) (R.obj V) n z)))
    (congrArg (fun L : _ →ₗ[R.obj V] _ => (L : _ → _))
      (cechDiffTerm_hom V n (single x)).symm)) ?_
  exact (LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom (ι_diffDesc F V n (single x)))
    (Cech.genTerm x.elts (fam (single x)) (singleIdx x)
      (exists_dvd_fam_single x) (R.obj V) n z)).symm

/-- **The leg respects the degree-zero identification with the ring of sections.** -/
theorem legAt_comp_augDesc {V : Cᵒᵖ} (x : F.Gen V) (z : Cech.cechTerm x.elts (R.obj V) 0) :
    (augDesc F V).hom ((legAt 0 x).hom z) =
      LocalCohomology.cechTermZeroEquiv x.elts (ModuleCat.of (R.obj V) (R.obj V)) z :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι_augDesc F V (single x)))
      (Cech.genTerm x.elts (fam (single x)) (singleIdx x)
        (exists_dvd_fam_single x) (R.obj V) 0 z)).trans
    (congrArg
      (fun m : (Cech.cechComplex x.elts (R.obj V)).X 0 ⟶
          ModuleCat.of (R.obj V) (R.obj V) => m.hom z)
      (PairSite.cechZeroIso_cechGenMap x.elts (fam (single x))
        (singleIdx x) (exists_dvd_fam_single x)
        (ModuleCat.of (R.obj V) (R.obj V))))

end Local

/-! ### A family distinguished over every object of a category mapping to the base -/

variable {D : Type u} [Category.{u} D] (G : D ⥤ C) (F : FamilySystem R) {r : ℕ}
  (f : ∀ V : Dᵒᵖ, Fin r → (G.op ⋙ R).obj V)
  (hf : ∀ {V W : Dᵒᵖ} (a : V ⟶ W) (i : Fin r), ((G.op ⋙ R).map a).hom (f V i) = f W i)
  (hmem : ∀ V : Dᵒᵖ, F.Mem (V := G.op.obj V) (f V))

/-- Restriction of presheaves of modules along a functor is additive, being computed on
sections. -/
instance additive_pushforward₀ {D' : Type u} [Category.{u} D'] (G' : D' ⥤ C)
    (R' : Cᵒᵖ ⥤ RingCat.{u}) : (PresheafOfModules.pushforward₀.{u} G' R').Additive where
  map_add := rfl

/-- The same, in the spelling of a presheaf of commutative rings. -/
instance additive_pushforward₀OfCommRingCat :
    (PresheafOfModules.pushforward₀OfCommRingCat.{u} G R).Additive where
  map_add := rfl

/-- **The distinguished family over the image of an object** cut out of a compatible family. -/
def genOf (V : Dᵒᵖ) : F.Gen (G.op.obj V) := ⟨r, f V, hmem V⟩

/-- The arity of `genOf G F f hmem V` is `r`. -/
@[simp]
theorem genOf_arity (V : Dᵒᵖ) : (genOf G F f hmem V).arity = r := rfl

/-- The members of `genOf G F f hmem V` are the entries of `f V`. -/
@[simp]
theorem genOf_elts (V : Dᵒᵖ) : (genOf G F f hmem V).elts = f V := rfl

/-- **The comparison over one object, degreewise**: the leg of the colimit over `G V` at the
family `f|_V`. -/
abbrev legApp (n : ℕ) (V : Dᵒᵖ) :
    (Cech.cechComplex (f V) ((G.op ⋙ R).obj V)).X n ⟶
      (colimit (cechTermDiagram F (G.op.obj V) n) : ModuleCat.{u} (R.obj (G.op.obj V))) :=
  legAt n (genOf G F f hmem V)

include hf in
/-- **The naturality of the comparison**, on elements. -/
theorem legApp_naturality (n : ℕ) {V W : Dᵒᵖ} (a : V ⟶ W)
    (x : Cech.cechTerm (f V) ((G.op ⋙ R).obj V) n) :
    (legApp G F f hmem n W).hom
        (CechSemilinear.termMap ((G.op ⋙ R).map a).hom (f V) (f W) (hf a) n x) =
      (transportDesc F (G.op.map a) n).hom ((legApp G F f hmem n V).hom x) :=
  legAt_mk_naturality n (G.op.map a) (f V) (f W) (hf a) (hmem V) (hmem W) x

include hf in
/-- **The degree-`n` component of the comparison**, as a map of presheaves of modules into the
restriction of the presheaf of Čech complexes of the family system along `G`. -/
def legTerm (n : ℕ) :
    CechPresheaf.cechPresheafTerm (G.op ⋙ R) f hf n ⟶
      (PresheafOfModules.pushforward₀OfCommRingCat G R).obj (cechTermPresheaf F n) where
  app V := legApp G F f hmem n V
  naturality {_V _W} a :=
    ModuleCat.hom_ext (LinearMap.ext fun x => legApp_naturality G F f hf hmem n a x)

include hf in
/-- **The comparison from the sectionwise Čech complex of a family distinguished over every object
into the restriction along `G` of the presheaf of Čech complexes of the family system**, in
nonnegative degrees. -/
def legNat : CechPresheaf.cechPresheafComplexNat (G.op ⋙ R) f hf ⟶
    ((PresheafOfModules.pushforward₀OfCommRingCat G R).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (cechComplexPresheafNat F) where
  f n := legTerm G F f hf hmem n
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    simp only [Functor.mapHomologicalComplex_obj_d, CechPresheaf.cechPresheafComplexNat,
      CochainComplex.of_d, cechComplexPresheafNat_d]
    refine PresheafOfModules.hom_ext fun V =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact (legAt_comm n (genOf G F f hmem V) x).symm

/-- The degree-`n` component of `legNat G F f hf hmem` at `V` is `legApp G F f hmem n V`. -/
theorem legNat_f_app (n : ℕ) (V : Dᵒᵖ) :
    ((legNat G F f hf hmem).f n).app V = legApp G F f hmem n V :=
  rfl

include hf in
/-- **The comparison is a map over `R`**, in degree zero: followed by the restriction along `G` of
the augmentation of the presheaf of Čech complexes of the family system, it is the augmentation of
the sectionwise Čech complex. -/
theorem legTerm_zero_comp_cechAugZero :
    legTerm G F f hf hmem 0 ≫
        (PresheafOfModules.pushforward₀OfCommRingCat G R).map (cechAugZero F) =
      CechPresheaf.cechPresheafAugmentationZero (G.op ⋙ R) f hf :=
  PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => legAt_comp_augDesc (genOf G F f hmem V) x)

end Stacks.CechFamilySystem

end
