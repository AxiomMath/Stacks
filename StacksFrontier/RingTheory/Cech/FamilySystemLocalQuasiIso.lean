module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.HomologyLocallyBijective
public import StacksFrontier.RingTheory.Cech.FamilySystemLeg
public import StacksFrontier.RingTheory.Cech.FamilySystemQuasiIso
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures

/-!
# The leg of a distinguished family is a local quasi-isomorphism

Let `R` be a presheaf of commutative rings on `C`, `F` a family system on it, `G : D ⥤ C` a
functor, `J` a Grothendieck topology on `D`, and `f₁, …, f_r` a family given over every object of
`D`, compatible with restriction and distinguished over every object. The leg
`Stacks.CechFamilySystem.legNat` of `FamilySystemLeg.lean` compares the sectionwise Čech complex of
`f` with the restriction along `G` of the presheaf of Čech complexes of `F`. This file proves that
its maps of homology presheaves are **locally injective and locally surjective** for `J` as soon as
finitely many distinguished families over an object always span one ideal locally
(`Stacks.CechFamilySystem.LocallySpanEq`) — which is what a family system of local generators of a
sheaf of ideals satisfies. By `PresheafOfModules.quasiIso_sheafification_map_of_isLocallyBijective`
the leg then becomes a quasi-isomorphism after sheafification.

This is the step of [Stacks, Tag 099E] which says that the sheafified presheaves of Čech complexes
of two finitely generated ideals generating `ℐ|_U` agree, read for the colimit over all of them at
once. The covering depends on the section: a section of the colimit comes from one stage, a finite
set of distinguished families, and only those finitely many families can be made to span one ideal
by passing to a covering. That is why the conclusion is local bijectivity sectionwise and not a
quasi-isomorphism over a covering sieve.

## The chase

*Surjectivity* (`Stacks.CechFamilySystem.exists_mem_sieve_transportDesc_eq`). A cycle of the
colimit over `G V` comes from a cochain `z₀` of a stage `S₀` which is a cycle at a later stage;
enlarge that stage to contain `f|_V` and call it `T`. Along a covering sieve the restrictions of
the finitely many families of `T` span one ideal, so the transition from the singleton `{f|_W}`
into the restriction of `T` is a quasi-isomorphism
(`Stacks.CechFamilySystem.quasiIso_cechDiagram_map_genOf`), and so is the reindexing
`Č(f|_W) ⟶ Č(fam {f|_W})`; lifting the restricted cycle twice along them gives a cycle of
`Č(f|_W)` up to boundaries.

*Injectivity* (`Stacks.CechFamilySystem.exists_mem_sieve_termMap_eq_d`). A cycle `z'` of `Č(f|_V)`
whose leg is a boundary in the colimit is a boundary at some stage `T₁ ∋ f|_V`. Transporting along
an arrow of a covering sieve on which the families of `T₁` span one ideal and using the stage-level
naturality of the reindexing (`Stacks.CechFamilySystem.singleLeg_mk_naturality`), the reindexed
restriction of `z'` is a boundary after a quasi-isomorphic transition, hence a boundary, and so is
the restriction of `z'` itself.

The elementwise consequences of a quasi-isomorphism of complexes of modules, and the sectionwise
criteria for local bijectivity of a map of homology presheaves, are those of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/HomologyLocallyBijective.lean`.

## Main results

* `Stacks.CechFamilySystem.isLocallySurjective_homologyMap_legNat` and
  `Stacks.CechFamilySystem.isLocallyInjective_homologyMap_legNat`: **the leg is locally bijective
  on homology.**

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.CechFamilySystem

open FamilySystem

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}} {F : FamilySystem R}

/-! ### Elements of the filtered colimit at an object -/

section Colimit

variable {V : Cᵒᵖ} [Nonempty (F.GenSet V)]

/-- **Every section of the colimit comes from a stage.** -/
theorem exists_colimit_ι_hom_eq (n : ℕ)
    (w : (colimit (cechTermDiagram F V n) : ModuleCat.{u} (R.obj V))) :
    ∃ (S : F.GenSet V) (z : Cech.cechTerm (fam S) (R.obj V) n),
      (colimit.ι (cechTermDiagram F V n) S).hom z = w :=
  Concrete.colimit_exists_rep (cechTermDiagram F V n) w

/-- **A cochain of a stage dying in the colimit already dies at a later stage.** -/
theorem exists_le_map_eq_zero (n : ℕ) (S : F.GenSet V) (z : Cech.cechTerm (fam S) (R.obj V) n)
    (h : (colimit.ι (cechTermDiagram F V n) S).hom z = 0) :
    ∃ (T : F.GenSet V) (hST : S ≤ T), (((cechDiagram F V).map (homOfLE hST)).f n).hom z = 0 := by
  obtain ⟨T, i, hi⟩ :=
    CategoryTheory.Limits.Concrete.colimit_rep_eq_zero (R.obj V) (cechTermDiagram F V n) S z h
  exact ⟨T, leOfHom i, hi⟩

end Colimit

/-- A map of complexes of modules commutes with the differentials, on elements. -/
theorem hom_comm_apply {A : Type u} [Ring A] {c : ComplexShape ℕ}
    {K L : HomologicalComplex (ModuleCat.{u} A) c} (φ : K ⟶ L) (i j : ℕ) (x : K.X i) :
    (φ.f j).hom ((K.d i j).hom x) = (L.d i j).hom ((φ.f i).hom x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.comm i j)) x).symm

/-- A map of complexes of modules sends elements killed by a differential to such elements. -/
private theorem d_hom_apply_eq_zero {A : Type u} [Ring A] {c : ComplexShape ℕ}
    {K L : HomologicalComplex (ModuleCat.{u} A) c} (φ : K ⟶ L) (i j : ℕ) (x : K.X i)
    (h : (K.d i j).hom x = 0) : (L.d i j).hom ((φ.f i).hom x) = 0 :=
  (hom_comm_apply φ i j x).symm.trans ((congrArg _ h).trans (map_zero _))

/-- The transitions of the diagram compose, on elements. -/
theorem cechDiagram_map_map_apply (V : Cᵒᵖ) {S T U : F.GenSet V} (h₁ : S ≤ T) (h₂ : T ≤ U)
    (n : ℕ) (z : Cech.cechTerm (fam S) (R.obj V) n) :
    (((cechDiagram F V).map (homOfLE h₂)).f n).hom
        ((((cechDiagram F V).map (homOfLE h₁)).f n).hom z) =
      (((cechDiagram F V).map (homOfLE (h₁.trans h₂))).f n).hom z :=
  (LinearMap.congr_fun (congrArg
    (fun m : Cech.cechComplex (fam S) (R.obj V) ⟶ Cech.cechComplex (fam U) (R.obj V) =>
      ModuleCat.Hom.hom (m.f n))
    ((cechDiagram F V).map_comp (homOfLE h₁) (homOfLE h₂))) z).symm

/-- The restriction of Čech cochains along a ring map commutes with every differential of the
Čech complex, including the zero ones outside the shape. -/
theorem termMap_cechComplex_d {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) {r : ℕ}
    (f : Fin r → A) (g : Fin r → B) (h : ∀ i, φ (f i) = g i) (i j : ℕ)
    (x : Cech.cechTerm f A i) :
    CechSemilinear.termMap φ f g h j (((Cech.cechComplex f A).d i j).hom x) =
      ((Cech.cechComplex g B).d i j).hom (CechSemilinear.termMap φ f g h i x) := by
  by_cases hij : (ComplexShape.up ℕ).Rel i j
  · obtain rfl : i + 1 = j := hij
    have hd : ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A),
        ((Cech.cechComplex f A).d i (i + 1)).hom = Cech.cechD f A i := fun f => by
      simp only [Cech.cechComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
      rfl
    rw [hd, hd]
    exact CechSemilinear.termMap_cechD φ f g h i x
  · rw [HomologicalComplex.shape _ _ _ hij, HomologicalComplex.shape _ _ _ hij]
    exact map_zero (CechSemilinear.termMap φ f g h j)

/-- **A cochain whose leg is a boundary in the colimit is a boundary at a stage**: if the leg of a
cochain `z'` of `Č(g)` is the image of a boundary of a stage, then the image of `z'` at some stage
containing `g` is a boundary. -/
theorem exists_le_cechDiagram_map_singleLeg_eq_d {V : Cᵒᵖ} (g : F.Gen V) (i : ℕ)
    (z' : Cech.cechTerm g.elts (R.obj V) i) (S₀ : F.GenSet V)
    (y₀ : Cech.cechTerm (fam S₀) (R.obj V) ((ComplexShape.up ℕ).prev i))
    (hy : (legAt i g).hom z' = (colimit.ι (cechTermDiagram F V i) S₀).hom
      (((Cech.cechComplex (fam S₀) (R.obj V)).d ((ComplexShape.up ℕ).prev i) i).hom y₀)) :
    ∃ (T₁ : F.GenSet V) (hT : single g ≤ T₁)
      (y : Cech.cechTerm (fam T₁) (R.obj V) ((ComplexShape.up ℕ).prev i)),
      (((cechDiagram F V).map (homOfLE hT)).f i).hom (((singleLeg g).f i).hom z') =
        ((Cech.cechComplex (fam T₁) (R.obj V)).d ((ComplexShape.up ℕ).prev i) i).hom y := by
  have : Nonempty (F.GenSet V) := ⟨single g⟩
  have hTl : single g ≤ single g ⊔ S₀ := le_sup_left
  have hTr : S₀ ≤ single g ⊔ S₀ := le_sup_right
  have hu : (colimit.ι (cechTermDiagram F V i) (single g ⊔ S₀)).hom
      ((((cechDiagram F V).map (homOfLE hTl)).f i).hom (((singleLeg g).f i).hom z') -
        (((cechDiagram F V).map (homOfLE hTr)).f i).hom
          (((Cech.cechComplex (fam S₀) (R.obj V)).d ((ComplexShape.up ℕ).prev i) i).hom y₀)) =
      0 :=
    (map_sub _ _ _).trans (sub_eq_zero.2 ((colimit_ι_apply_of_le F _ i _ _).trans
      (hy.trans (colimit_ι_apply_of_le F _ i _ _).symm)))
  obtain ⟨T₁, hTT₁, hu₁⟩ := exists_le_map_eq_zero i _ _ hu
  exact ⟨T₁, hTl.trans hTT₁,
    (((cechDiagram F V).map (homOfLE (hTr.trans hTT₁))).f ((ComplexShape.up ℕ).prev i)).hom y₀,
    (cechDiagram_map_map_apply _ hTl hTT₁ i _).symm.trans
      ((sub_eq_zero.1 ((map_sub _ _ _).symm.trans hu₁)).trans
        ((cechDiagram_map_map_apply _ hTr hTT₁ i _).trans
          (hom_comm_apply ((cechDiagram F V).map (homOfLE (hTr.trans hTT₁))) _ i y₀)))⟩

/-! ### The chase -/

section Chase

variable {D : Type u} [Category.{u} D] {G : D ⥤ C} {r : ℕ}
  {f : ∀ V : Dᵒᵖ, Fin r → (G.op ⋙ R).obj V}
  (hf : ∀ {V W : Dᵒᵖ} (a : V ⟶ W) (i : Fin r), ((G.op ⋙ R).map a).hom (f V i) = f W i)
  (hmem : ∀ V : Dᵒᵖ, F.Mem (V := G.op.obj V) (f V))

include hf in
/-- **The restriction of the distinguished family over `V` is the one over `W`.** -/
theorem gen_map_genOf {V W : Dᵒᵖ} (a : V ⟶ W) :
    Gen.map (G.op.map a) (genOf G F f hmem V) = genOf G F f hmem W :=
  Gen.ext_elts _ _ (funext fun i => hf a i)

variable (G F) in
/-- **Finitely many distinguished families over an object span one ideal locally**: for every
object `V` of `D` and every finite set of distinguished families over `G V`, there is a covering
sieve of `V` along each arrow of which their restrictions all span the same ideal. -/
def LocallySpanEq (J : GrothendieckTopology D) : Prop :=
  ∀ (V : D) (T : Finset (F.Gen (G.op.obj (op V)))), ∃ S : Sieve V, S ∈ J V ∧
    ∀ ⦃W : D⦄ (b : W ⟶ V), S b → ∀ x ∈ T, ∀ y ∈ T,
      Ideal.span (Set.range (Gen.map (G.op.map b.op) x).elts) =
        Ideal.span (Set.range (Gen.map (G.op.map b.op) y).elts)

variable (J : GrothendieckTopology D)

include hf in
/-- Over an arrow along which a finite set `T` of distinguished families containing `f|_V` spans
one ideal, the transition out of the singleton `{f|_W}` into the restriction of `T` is a
quasi-isomorphism. -/
theorem quasiIso_cechDiagram_map_genOf {V W : D} (b : W ⟶ V) (T : F.GenSet (G.op.obj (op V)))
    (hT : genOf G F f hmem (op V) ∈ T.carrier)
    (hspan : ∀ x ∈ T.carrier, ∀ y ∈ T.carrier,
      Ideal.span (Set.range (Gen.map (G.op.map b.op) x).elts) =
        Ideal.span (Set.range (Gen.map (G.op.map b.op) y).elts)) :
    ∃ h : single (genOf G F f hmem (op W)) ≤ GenSet.map (G.op.map b.op) T,
      QuasiIso ((cechDiagram F (G.op.obj (op W))).map (homOfLE h)) := by
  have hmemW : genOf G F f hmem (op W) ∈ (GenSet.map (G.op.map b.op) T).carrier := by
    rw [GenSet.map_carrier, ← gen_map_genOf hf hmem b.op]
    exact Finset.mem_image_of_mem _ hT
  refine ⟨(single_le_iff _ _).2 hmemW, quasiIso_cechDiagram_map_single _ fun y hy => ?_⟩
  obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hy
  rw [← gen_map_genOf hf hmem b.op]
  exact hspan y₀ hy₀ _ hT

include hf in
/-- **Local surjectivity of the leg on homology, at the level of the stages.** Let `z₀` be a
cochain of a stage over `G V` whose image in the colimit is a cycle. Along every arrow `b` of a
covering sieve of `V`, the restriction of that image is the leg of a cycle of the Čech complex of
`f|_W`, plus two boundaries coming from stages over `G W`. -/
theorem exists_mem_sieve_transportDesc_eq (hloc : LocallySpanEq F G J) (i : ℕ) (V : D)
    (S₀ : F.GenSet (G.op.obj (op V))) (z₀ : Cech.cechTerm (fam S₀) (R.obj (G.op.obj (op V))) i)
    (hz₀ : (colimit.ι (cechTermDiagram F (G.op.obj (op V)) ((ComplexShape.up ℕ).next i)) S₀).hom
      (((Cech.cechComplex (fam S₀) (R.obj (G.op.obj (op V)))).d i
        ((ComplexShape.up ℕ).next i)).hom z₀) = 0) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : D⦄ (b : W ⟶ V), S b →
      ∃ z' : Cech.cechTerm (genOf G F f hmem (op W)).elts (R.obj (G.op.obj (op W))) i,
        ((Cech.cechComplex (genOf G F f hmem (op W)).elts (R.obj (G.op.obj (op W)))).d i
          ((ComplexShape.up ℕ).next i)).hom z' = 0 ∧
        ∃ (T₁ T₂ : F.GenSet (G.op.obj (op W)))
          (y₁ : Cech.cechTerm (fam T₁) (R.obj (G.op.obj (op W))) ((ComplexShape.up ℕ).prev i))
          (y₂ : Cech.cechTerm (fam T₂) (R.obj (G.op.obj (op W))) ((ComplexShape.up ℕ).prev i)),
          (transportDesc F (G.op.map b.op) i).hom
              ((colimit.ι (cechTermDiagram F (G.op.obj (op V)) i) S₀).hom z₀) =
            (legAt i (genOf G F f hmem (op W))).hom z' +
              (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i) T₁).hom
                (((Cech.cechComplex (fam T₁) (R.obj (G.op.obj (op W)))).d
                  ((ComplexShape.up ℕ).prev i) i).hom y₁) +
              (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i) T₂).hom
                (((Cech.cechComplex (fam T₂) (R.obj (G.op.obj (op W)))).d
                  ((ComplexShape.up ℕ).prev i) i).hom y₂) := by
  set j := (ComplexShape.up ℕ).next i
  set k := (ComplexShape.up ℕ).prev i
  have : Nonempty (F.GenSet (G.op.obj (op V))) := ⟨single (genOf G F f hmem (op V))⟩
  obtain ⟨S₁, h01, hz₁⟩ := exists_le_map_eq_zero j S₀ _ hz₀
  set T := S₁ ⊔ single (genOf G F f hmem (op V))
  have h0T : S₀ ≤ T := h01.trans le_sup_left
  have hz₁cyc : (((cechDiagram F (G.op.obj (op V))).obj T).d i j).hom
      ((((cechDiagram F (G.op.obj (op V))).map (homOfLE h0T)).f i).hom z₀) = 0 :=
    (hom_comm_apply ((cechDiagram F _).map (homOfLE h0T)) i j z₀).symm.trans
      ((cechDiagram_map_map_apply _ h01 le_sup_left j _).symm.trans
        ((congrArg _ hz₁).trans (map_zero _)))
  set z₁ := (((cechDiagram F (G.op.obj (op V))).map (homOfLE h0T)).f i).hom z₀
  have hw₁ : (colimit.ι (cechTermDiagram F (G.op.obj (op V)) i) S₀).hom z₀ =
      (colimit.ι (cechTermDiagram F (G.op.obj (op V)) i) T).hom z₁ :=
    (colimit_ι_apply_of_le F _ i (homOfLE h0T) z₀).symm
  obtain ⟨Sv, hSv, hspan⟩ := hloc V T.carrier
  refine ⟨Sv, hSv, fun W b hb => ?_⟩
  set a := G.op.map b.op
  set z₂ := ((cechTransport F a T).f i).hom z₁
  have hz₂ : (((cechDiagram F (G.op.obj (op W))).obj (GenSet.map a T)).d i j).hom z₂ = 0 :=
    d_hom_apply_eq_zero (cechTransport F a T) i j z₁ hz₁cyc
  obtain ⟨hle, hqis⟩ := quasiIso_cechDiagram_map_genOf hf hmem b T
    (Finset.mem_of_subset (le_sup_right : single _ ≤ T) (Finset.mem_singleton_self _))
    (hspan b hb)
  obtain ⟨z₃, hz₃, y₃, h₃⟩ := HomologicalComplex.exists_cycle_eq_add_d_of_quasiIsoAt
    ((cechDiagram F (G.op.obj (op W))).map (homOfLE hle)) i z₂ hz₂
  have := quasiIso_singleLeg (genOf G F f hmem (op W))
  obtain ⟨z₄, hz₄, y₄, h₄⟩ := HomologicalComplex.exists_cycle_eq_add_d_of_quasiIsoAt
    (singleLeg (genOf G F f hmem (op W))) i z₃ hz₃
  refine ⟨z₄, hz₄, single (genOf G F f hmem (op W)), GenSet.map a T, y₄, y₃, ?_⟩
  have e₁ : (transportDesc F a i).hom
      ((colimit.ι (cechTermDiagram F (G.op.obj (op V)) i) S₀).hom z₀) =
      (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i) (GenSet.map a T)).hom z₂ :=
    (congrArg (transportDesc F a i).hom hw₁).trans (transportDesc_ι_apply F a i T z₁)
  have e₂ : (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i) (GenSet.map a T)).hom z₂ =
      (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i) (single (genOf G F f hmem (op W)))).hom
          z₃ +
        (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i) (GenSet.map a T)).hom
          (((Cech.cechComplex (fam (GenSet.map a T)) (R.obj (G.op.obj (op W)))).d k i).hom y₃) :=
    (congrArg (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i) (GenSet.map a T)).hom h₃).trans
      ((map_add _ _ _).trans (congrArg (· + _)
        (colimit_ι_apply_of_le F _ i (homOfLE hle) z₃)))
  have e₃ : (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i)
      (single (genOf G F f hmem (op W)))).hom z₃ =
      (legAt i (genOf G F f hmem (op W))).hom z₄ +
        (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i)
          (single (genOf G F f hmem (op W)))).hom
          (((Cech.cechComplex (fam (single (genOf G F f hmem (op W))))
            (R.obj (G.op.obj (op W)))).d k i).hom y₄) :=
    (congrArg (colimit.ι (cechTermDiagram F (G.op.obj (op W)) i)
      (single (genOf G F f hmem (op W)))).hom h₄).trans (map_add _ _ _)
  rw [e₁, e₂, e₃]

include hf in
/-- If the image of a cochain `z'` of `Č(f|_V)` at a stage `T₁ ∋ f|_V` is the boundary of `y`, then
the image of the restriction of `z'` in the restriction of `T₁` is the boundary of the transport
of `y`. -/
theorem cechDiagram_map_singleLeg_termMap_eq_d {V W : D} (b : W ⟶ V)
    (T₁ : F.GenSet (G.op.obj (op V))) (i : ℕ) (hT₁ : single (genOf G F f hmem (op V)) ≤ T₁)
    (hle : single (genOf G F f hmem (op W)) ≤ GenSet.map (G.op.map b.op) T₁)
    (z' : Cech.cechTerm (genOf G F f hmem (op V)).elts (R.obj (G.op.obj (op V))) i)
    (y : Cech.cechTerm (fam T₁) (R.obj (G.op.obj (op V))) ((ComplexShape.up ℕ).prev i))
    (hv : (((cechDiagram F (G.op.obj (op V))).map (homOfLE hT₁)).f i).hom
        (((singleLeg (genOf G F f hmem (op V))).f i).hom z') =
      ((Cech.cechComplex (fam T₁) (R.obj (G.op.obj (op V)))).d
        ((ComplexShape.up ℕ).prev i) i).hom y) :
    (((cechDiagram F (G.op.obj (op W))).map (homOfLE hle)).f i).hom
        (((singleLeg (genOf G F f hmem (op W))).f i).hom
          (CechSemilinear.termMap ((G.op ⋙ R).map b.op).hom (f (op V)) (f (op W)) (hf b.op) i
            z')) =
      (((Cech.cechComplex (fam (GenSet.map (G.op.map b.op) T₁)) (R.obj (G.op.obj (op W)))).d
        ((ComplexShape.up ℕ).prev i) i).hom
        (((cechTransport F (G.op.map b.op) T₁).f ((ComplexShape.up ℕ).prev i)).hom y)) := by
  have hsx : single (genOf G F f hmem (op W)) ≤
      GenSet.map (G.op.map b.op) (single (genOf G F f hmem (op V))) :=
    le_of_eq (by rw [map_single, gen_map_genOf hf hmem b.op])
  have hmono : GenSet.map (G.op.map b.op) (single (genOf G F f hmem (op V))) ≤
      GenSet.map (G.op.map b.op) T₁ :=
    GenSet.map_monotone (G.op.map b.op) hT₁
  have e₁ := cechDiagram_map_map_apply (G.op.obj (op W)) hsx hmono i
    (((singleLeg (genOf G F f hmem (op W))).f i).hom
      (CechSemilinear.termMap ((G.op ⋙ R).map b.op).hom (f (op V)) (f (op W)) (hf b.op) i z'))
  have e₂ := singleLeg_mk_naturality i (G.op.map b.op) (f (op V)) (f (op W)) (hf b.op)
    (hmem (op V)) (hmem (op W)) hsx z'
  have e₃ := LinearMap.congr_fun (congrArg
    (fun m => ModuleCat.Hom.hom (HomologicalComplex.Hom.f m i))
    (cechDiagram_map_comp_cechTransport F (G.op.map b.op) (homOfLE hT₁)))
    (((singleLeg (genOf G F f hmem (op V))).f i).hom z')
  have e₄ := congrArg ((cechTransport F (G.op.map b.op) T₁).f i).hom hv
  have e₅ := hom_comm_apply (cechTransport F (G.op.map b.op) T₁) ((ComplexShape.up ℕ).prev i) i y
  exact e₁.symm.trans ((congrArg (((cechDiagram F (G.op.obj (op W))).map
    (homOfLE hmono)).f i).hom e₂).trans (e₃.symm.trans (e₄.trans e₅)))

include hf in
/-- **Local injectivity of the leg on homology, at the level of the stages.** Let `z'` be a cycle
of the Čech complex of `f|_V` whose leg is the image of a boundary of a stage. Along every arrow
of a covering sieve of `V` the restriction of `z'` is a boundary. -/
theorem exists_mem_sieve_termMap_eq_d (hloc : LocallySpanEq F G J) (i : ℕ) (V : D)
    (z' : Cech.cechTerm (genOf G F f hmem (op V)).elts (R.obj (G.op.obj (op V))) i)
    (hz' : ((Cech.cechComplex (genOf G F f hmem (op V)).elts (R.obj (G.op.obj (op V)))).d i
      ((ComplexShape.up ℕ).next i)).hom z' = 0)
    (S₀ : F.GenSet (G.op.obj (op V)))
    (y₀ : Cech.cechTerm (fam S₀) (R.obj (G.op.obj (op V))) ((ComplexShape.up ℕ).prev i))
    (hy : (legAt i (genOf G F f hmem (op V))).hom z' =
      (colimit.ι (cechTermDiagram F (G.op.obj (op V)) i) S₀).hom
        (((Cech.cechComplex (fam S₀) (R.obj (G.op.obj (op V)))).d
          ((ComplexShape.up ℕ).prev i) i).hom y₀)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃W : D⦄ (b : W ⟶ V), S b →
      ∃ y' : Cech.cechTerm (genOf G F f hmem (op W)).elts (R.obj (G.op.obj (op W)))
          ((ComplexShape.up ℕ).prev i),
        CechSemilinear.termMap ((G.op ⋙ R).map b.op).hom (f (op V)) (f (op W)) (hf b.op) i z' =
          ((Cech.cechComplex (genOf G F f hmem (op W)).elts (R.obj (G.op.obj (op W)))).d
            ((ComplexShape.up ℕ).prev i) i).hom y' := by
  obtain ⟨T₁, hT₁, y₁, hv⟩ :=
    exists_le_cechDiagram_map_singleLeg_eq_d (genOf G F f hmem (op V)) i z' S₀ y₀ hy
  obtain ⟨Sv, hSv, hspan⟩ := hloc V T₁.carrier
  refine ⟨Sv, hSv, fun W b hb => ?_⟩
  obtain ⟨hle, hqis⟩ := quasiIso_cechDiagram_map_genOf hf hmem b T₁
    ((single_le_iff _ _).1 hT₁) (hspan b hb)
  have hc := cechDiagram_map_singleLeg_termMap_eq_d hf hmem b T₁ i hT₁ hle z' y₁ hv
  have hcyc₀ : ((Cech.cechComplex (genOf G F f hmem (op W)).elts (R.obj (G.op.obj (op W)))).d i
      ((ComplexShape.up ℕ).next i)).hom
        (CechSemilinear.termMap ((G.op ⋙ R).map b.op).hom (f (op V)) (f (op W)) (hf b.op) i
          z') = 0 :=
    (termMap_cechComplex_d ((G.op ⋙ R).map b.op).hom (f (op V)) (f (op W)) (hf b.op) i _
      z').symm.trans ((congrArg _ hz').trans (map_zero _))
  have hcyc : ((Cech.cechComplex (fam (single (genOf G F f hmem (op W))))
      (R.obj (G.op.obj (op W)))).d i ((ComplexShape.up ℕ).next i)).hom
        (((singleLeg (genOf G F f hmem (op W))).f i).hom
          (CechSemilinear.termMap ((G.op ⋙ R).map b.op).hom (f (op V)) (f (op W)) (hf b.op) i
            z')) = 0 :=
    d_hom_apply_eq_zero (singleLeg (genOf G F f hmem (op W))) i _ _ hcyc₀
  obtain ⟨y₅, h₅⟩ := HomologicalComplex.exists_d_eq_of_quasiIsoAt
    ((cechDiagram F (G.op.obj (op W))).map (homOfLE hle)) i _ hcyc _ hc
  have := quasiIso_singleLeg (genOf G F f hmem (op W))
  exact HomologicalComplex.exists_d_eq_of_quasiIsoAt (singleLeg (genOf G F f hmem (op W))) i _
    hcyc₀ y₅ h₅

/-- The differential of the presheaf of Čech complexes of a compatible family, over one object, is
the Čech differential of the ring of sections there. -/
theorem cechPresheafComplexNat_d_app_hom_apply {D : Type u} [Category.{u} D]
    (R' : Dᵒᵖ ⥤ CommRingCat.{u}) {r : ℕ} (f : ∀ V : Dᵒᵖ, Fin r → R'.obj V)
    (hf : ∀ {V W : Dᵒᵖ} (a : V ⟶ W) (i : Fin r), (R'.map a).hom (f V i) = f W i) (V : Dᵒᵖ)
    (i j : ℕ) (z : Cech.cechTerm (f V) (R'.obj V) i) :
    (((CechPresheaf.cechPresheafComplexNat R' f hf).d i j).app V).hom z =
      ((Cech.cechComplex (f V) (R'.obj V)).d i j).hom z := by
  have hm := (CechPresheaf.cechComplexIsoEvaluation R' f hf V).hom.comm i j
  simp only [CechPresheaf.cechComplexIsoEvaluation] at hm
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hm) z

include hf in
/-- **The leg is locally surjective on homology.** -/
theorem isLocallySurjective_homologyMap_legNat (hloc : LocallySpanEq F G J) (i : ℕ) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map
      (HomologicalComplex.homologyMap (legNat G F f hf hmem) i)) := by
  refine PresheafOfModules.isLocallySurjective_homologyMap _ i fun V z hz => ?_
  have : Nonempty (F.GenSet (G.op.obj (op V))) := ⟨single (genOf G F f hmem (op V))⟩
  obtain ⟨S₀, z₀, rfl⟩ := exists_colimit_ι_hom_eq (V := G.op.obj (op V)) i z
  have hz₀ := (hom_comm_apply (sectionsLegNat F (G.op.obj (op V)) S₀) i _ z₀).trans hz
  obtain ⟨Sv, hSv, H⟩ := exists_mem_sieve_transportDesc_eq hf hmem J hloc i V S₀ z₀ hz₀
  refine ⟨Sv, hSv, fun W b hb => ?_⟩
  obtain ⟨z', hz', T₁, T₂, y₁, y₂, he⟩ := H b hb
  refine ⟨z', (cechPresheafComplexNat_d_app_hom_apply _ f hf (op W) i _ z').trans hz',
    (colimit.ι (cechTermDiagram F (G.op.obj (op W)) _) T₁).hom y₁ +
      (colimit.ι (cechTermDiagram F (G.op.obj (op W)) _) T₂).hom y₂, ?_⟩
  have hd := (map_add (((cechComplexPresheafNat F).d ((ComplexShape.up ℕ).prev i) i).app
      (G.op.obj (op W))).hom
    ((colimit.ι (cechTermDiagram F (G.op.obj (op W)) _) T₁).hom y₁)
    ((colimit.ι (cechTermDiagram F (G.op.obj (op W)) _) T₂).hom y₂)).trans
    (congrArg₂ (· + ·) (hom_comm_apply (sectionsLegNat F (G.op.obj (op W)) T₁) _ i y₁).symm
      (hom_comm_apply (sectionsLegNat F (G.op.obj (op W)) T₂) _ i y₂).symm)
  exact he.trans ((add_assoc _ _ _).trans (congrArg _ hd.symm))

include hf in
/-- **The leg is locally injective on homology.** -/
theorem isLocallyInjective_homologyMap_legNat (hloc : LocallySpanEq F G J) (i : ℕ) :
    Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map
      (HomologicalComplex.homologyMap (legNat G F f hf hmem) i)) := by
  refine PresheafOfModules.isLocallyInjective_homologyMap _ i fun V z' hz' y hy => ?_
  have : Nonempty (F.GenSet (G.op.obj (op V))) := ⟨single (genOf G F f hmem (op V))⟩
  obtain ⟨S₀, y₀, rfl⟩ := exists_colimit_ι_hom_eq (V := G.op.obj (op V)) _ y
  have hz'' := (cechPresheafComplexNat_d_app_hom_apply _ f hf (op V) i _ z').symm.trans hz'
  have hy' := hy.trans (hom_comm_apply (sectionsLegNat F (G.op.obj (op V)) S₀) _ i y₀).symm
  obtain ⟨Sv, hSv, H⟩ := exists_mem_sieve_termMap_eq_d hf hmem J hloc i V z' hz'' S₀ y₀ hy'
  refine ⟨Sv, hSv, fun W b hb => ?_⟩
  obtain ⟨y', hy''⟩ := H b hb
  exact ⟨y', hy''.trans (cechPresheafComplexNat_d_app_hom_apply _ f hf (op W) _ i y').symm⟩

end Chase

end Stacks.CechFamilySystem

end
