module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystem
public import StacksFrontier.RingTheory.Idempotents.Gluing

/-!
# Gluing étale cohomology over the clopen subsets of a scheme

Let `T` be a scheme and `C = Γ(T, ⊤)`. Every idempotent `e` of `C` cuts out a clopen open
subscheme `T_e = D(e)` of `T`, and the clopen subsets of this form are stable under finite
intersections and complements. For an abelian sheaf `G` on the small étale site of `T`, the
classes of `H^q(T, G)` vanishing on `T_e` form an additive family of subgroups in the sense of
`StacksDraft.IdempotentGluing.IsAdditiveKernels`: this is the additivity of étale cohomology on a
disjoint union of two open subschemes.

Let `π : Y ⟶ T`. Pulling back `H^q(T, G) → H^q(Y, π⁻¹ G)` is then bijective as soon as it is
bijective on the germs at every point of `Spec C`, the germ at a prime `P` being the quotient by
the classes vanishing on some `T_e` with `e ∉ P`. This is the passage, in the proof of Stacks
Tag 0EZV, from the cofiltered limit of finite disjoint unions to the cohomology of the limit.

## Main definitions

* `Stacks.EtaleCohomology.IdempotentGluing.restrictKer`: the classes vanishing on an open `U e`.

## Main results

* `Stacks.EtaleCohomology.IdempotentGluing.bijective_pullback_pair`: étale cohomology of a disjoint
  union of two open subschemes is the product of their cohomologies.
* `Stacks.EtaleCohomology.IdempotentGluing.not_injective_etaleCohomologyPullback_of_range_subset`:
  pulling back to a scheme which misses one of two complementary opens kills the classes
  supported on it.
* `Stacks.EtaleCohomology.IdempotentGluing.isAdditiveKernels_restrictKer`: the kernels of
  restriction to a family of opens behaving like the clopens `D(e)` form an additive family.
* `Stacks.EtaleCohomology.IdempotentGluing.bijective_etaleCohomologyPullback_iff_germ`: pulling
  back along `π` is bijective if and only if it is bijective on the germs at every prime.

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite OrderDual
open AlgebraicGeometry AlgebraicGeometry.Scheme StacksDraft.IdempotentGluing

universe u

namespace Stacks.EtaleCohomology.IdempotentGluing

/-! ### Basic opens of idempotents -/

section BasicOpen

variable (T : Scheme.{u})

/-- For idempotent global sections `e ≤ f`, the basic open `D(e)` is contained in `D(f)`. -/
theorem basicOpen_mono {e f : Idem Γ(T, ⊤)} (h : e ≤ f) :
    T.basicOpen (e : Γ(T, ⊤)) ≤ T.basicOpen (f : Γ(T, ⊤)) := by
  rw [show (e : Γ(T, ⊤)) = e * f from h.symm, Scheme.basicOpen_mul]
  exact inf_le_right

/-- The basic opens of two disjoint idempotent global sections are disjoint. -/
theorem basicOpen_inf_eq_bot {e f : Idem Γ(T, ⊤)} (h : Disjoint e f) :
    T.basicOpen (e : Γ(T, ⊤)) ⊓ T.basicOpen (f : Γ(T, ⊤)) = ⊥ := by
  rw [← Scheme.basicOpen_mul, ← show ((e ⊓ f : Idem Γ(T, ⊤)) : Γ(T, ⊤)) = e * f from rfl,
    h.eq_bot]
  exact Scheme.basicOpen_zero T ⊤

/-- The basic open of the join `e ⊔ f` of two idempotent global sections is `D(e) ⊔ D(f)`. -/
theorem basicOpen_sup {e f : Idem Γ(T, ⊤)} :
    T.basicOpen ((e ⊔ f : Idem Γ(T, ⊤)) : Γ(T, ⊤)) =
      T.basicOpen (e : Γ(T, ⊤)) ⊔ T.basicOpen (f : Γ(T, ⊤)) := by
  ext x
  simp only [TopologicalSpace.Opens.coe_sup, Set.mem_union, SetLike.mem_coe]
  rw [Scheme.mem_basicOpen T _ x (Set.mem_univ x), Scheme.mem_basicOpen T _ x (Set.mem_univ x),
    Scheme.mem_basicOpen T _ x (Set.mem_univ x)]
  have h01 : ∀ {R : Type u} [CommRing R] [IsLocalRing R] {a : R}, IsIdempotentElem a →
      a = 0 ∨ a = 1 := fun {R} _ _ {a} ha => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
    · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp ha)
    · exact Or.inl (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp ha.one_sub))
  have he := h01 (e.2.map (T.presheaf.germ ⊤ x (Set.mem_univ x)).hom)
  have hf := h01 (f.2.map (T.presheaf.germ ⊤ x (Set.mem_univ x)).hom)
  rw [show ((e ⊔ f : Idem Γ(T, ⊤)) : Γ(T, ⊤)) = e + f - e * f from rfl, map_sub, map_add,
    map_mul]
  rcases he with he | he <;> rcases hf with hf | hf <;> simp [he, hf]

/-- The basic open of the top idempotent `1` is all of `T`. -/
theorem basicOpen_top : T.basicOpen ((⊤ : Idem Γ(T, ⊤)) : Γ(T, ⊤)) = ⊤ :=
  Scheme.basicOpen_one T

variable {T} {C : Type*} [CommRing C] (φ : C →+* Γ(T, ⊤))

/-- The image of an idempotent under a ring map to the global sections. -/
abbrev idemMap (e : Idem C) : Idem Γ(T, ⊤) := ⟨φ e, e.2.map φ⟩

/-- Mapping idempotents along `φ` is monotone. -/
theorem idemMap_mono : Monotone (idemMap φ) := fun e f h => by
  have h' : (e : C) * (f : C) = e := h
  change φ e * φ f = φ e
  rw [← map_mul, h']

/-- Mapping idempotents along `φ` sends `⊥` to `⊥`. -/
theorem idemMap_bot : idemMap φ ⊥ = ⊥ := Subtype.ext (map_zero φ)

/-- Mapping idempotents along `φ` sends `⊤` to `⊤`. -/
theorem idemMap_top : idemMap φ ⊤ = ⊤ := Subtype.ext (map_one φ)

/-- Mapping idempotents along `φ` preserves meets. -/
theorem idemMap_inf (e f : Idem C) : idemMap φ (e ⊓ f) = idemMap φ e ⊓ idemMap φ f :=
  Subtype.ext (map_mul φ (e : C) f)

/-- Mapping idempotents along `φ` preserves joins. -/
theorem idemMap_sup (e f : Idem C) : idemMap φ (e ⊔ f) = idemMap φ e ⊔ idemMap φ f :=
  Subtype.ext (show φ ((e : C) + f - e * f) = φ e + φ f - φ e * φ f by
    rw [map_sub, map_add, map_mul])

/-- The basic open `D(φ e)` cut out by the image of an idempotent `e` of `C` is monotone in `e`. -/
theorem basicOpen_idemMap_mono : Monotone fun e : Idem C => T.basicOpen (φ e) :=
  fun _ _ h => basicOpen_mono T (idemMap_mono φ h)

/-- The basic open cut out by the image of the idempotent `⊥ = 0` of `C` is empty. -/
theorem basicOpen_idemMap_bot : T.basicOpen (φ ((⊥ : Idem C) : C)) = ⊥ := by
  change T.basicOpen (φ 0) = ⊥
  rw [map_zero]
  exact Scheme.basicOpen_zero T ⊤

/-- The basic open cut out by the image of the idempotent `⊤ = 1` of `C` is all of `T`. -/
theorem basicOpen_idemMap_top : T.basicOpen (φ ((⊤ : Idem C) : C)) = ⊤ := by
  change T.basicOpen (φ 1) = ⊤
  rw [map_one]
  exact Scheme.basicOpen_one T

/-- The basic opens cut out by the images of two disjoint idempotents of `C` are disjoint. -/
theorem basicOpen_idemMap_inf (e f : Idem C) (h : Disjoint e f) :
    T.basicOpen (φ e) ⊓ T.basicOpen (φ f) = ⊥ := by
  rw [← Scheme.basicOpen_mul, ← map_mul, show (e : C) * f = ((e ⊓ f : Idem C) : C) from rfl,
    h.eq_bot]
  exact basicOpen_idemMap_bot φ

/-- The basic open cut out by the image of `e ⊔ f` is the union of those cut out by the images
of `e` and `f`. -/
theorem basicOpen_idemMap_sup (e f : Idem C) :
    T.basicOpen (φ ((e ⊔ f : Idem C) : C)) = T.basicOpen (φ e) ⊔ T.basicOpen (φ f) := by
  have h := basicOpen_sup T (e := idemMap φ e) (f := idemMap φ f)
  rwa [← idemMap_sup] at h

end BasicOpen

/-! ### Additivity for two disjoint opens -/

section Pair

variable {X : Scheme.{u}}

/-- For opens `A ≤ W` of `X`, the image of the inclusion `A ⟶ W` is the preimage of `A` under the
inclusion `W ⟶ X`. -/
theorem range_homOfLE {A W : X.Opens} (h : A ≤ W) :
    Set.range (X.homOfLE h).base = (W.ι).base ⁻¹' (A : Set X) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    change (X.homOfLE h ≫ W.ι).base a ∈ A
    rw [Scheme.homOfLE_ι]
    exact a.2
  · intro hz
    refine ⟨⟨W.ι.base z, hz⟩, ?_⟩
    apply W.ι.isOpenEmbedding.injective
    change (X.homOfLE h ≫ W.ι).base _ = _
    rw [Scheme.homOfLE_ι]
    rfl

/-- Disjoint opens have disjoint images. -/
private theorem disjoint_range_ι_of_inf_eq_bot {V V' : X.Opens} (h : V ⊓ V' = ⊥) :
    Disjoint (Set.range V.ι.base) (Set.range V'.ι.base) := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, Set.disjoint_iff_inter_eq_empty]
  simpa only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot] using
    congrArg (fun U : X.Opens => (U : Set X)) h

/-- Opens covering `X` have images covering `X`. -/
private theorem range_ι_union_of_sup_eq_top {V V' : X.Opens} (h : V ⊔ V' = ⊤) :
    Set.range V.ι.base ∪ Set.range V'.ι.base = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  simpa only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top] using
    congrArg (fun U : X.Opens => (U : Set X)) h

/-- Composing with the class of an isomorphism of sheaves is bijective on `Ext`. -/
theorem bijective_comp_mk₀_of_isIso {C : Type*} [Category C] [Abelian C] [HasExt.{u + 1} C]
    {A B B' : C} (φ : B ⟶ B') [IsIso φ] (q : ℕ) :
    Function.Bijective (fun y : Ext.{u + 1} A B q => y.comp (Ext.mk₀ φ) (add_zero q)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun z => z.comp (Ext.mk₀ (inv φ)) (add_zero q), fun z => ?_, fun z => ?_⟩
  · simp [Ext.mk₀_comp_mk₀]
  · simp [Ext.mk₀_comp_mk₀]

/-- **Additivity for two disjoint open subschemes.** If a scheme `W` is the disjoint union of the
images of open immersions `jA : A ⟶ W` and `jB : B ⟶ W`, pulling back along them, followed by
isomorphisms of sheaves, identifies `H^q(W, F)` with `H^q(A, ·) × H^q(B, ·)`. -/
theorem bijective_pullback_pair {W A B : Scheme.{u}} (jA : A ⟶ W) (jB : B ⟶ W)
    [IsOpenImmersion jA] [IsOpenImmersion jB]
    (hAB : Disjoint (Set.range jA.base) (Set.range jB.base))
    (hW : Set.range jA.base ∪ Set.range jB.base = Set.univ)
    (F : Sheaf (smallEtaleTopology W) Ab.{u + 1}) {GA : Sheaf (smallEtaleTopology A) Ab.{u + 1}}
    {GB : Sheaf (smallEtaleTopology B) Ab.{u + 1}} (φA : (smallEtalePullbackAb jA).obj F ⟶ GA)
    (φB : (smallEtalePullbackAb jB).obj F ⟶ GB) [IsIso φA] [IsIso φB] (q : ℕ) :
    Function.Bijective (fun x : Sheaf.H.{u + 1} F q =>
      (etaleCohomologyPullback jA φA q x, etaleCohomologyPullback jB φB q x)) := by
  classical
  let V : Bool → Scheme.{u} := fun b => Bool.rec B A b
  let j : ∀ b, V b ⟶ W := fun b => Bool.rec (motive := fun b => V b ⟶ W) jB jA b
  have : ∀ b, IsOpenImmersion (j b) := fun b => by cases b <;> assumption
  have hpi := bijective_etaleCohomologyPullback_pi j (fun a b hab => by
      cases a <;> cases b
      · exact absurd rfl hab
      · exact hAB.symm
      · exact hAB
      · exact absurd rfl hab)
    (by
      ext z
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      rcases (hW ▸ Set.mem_univ z : z ∈ Set.range jA.base ∪ Set.range jB.base) with hz | hz
      · exact ⟨true, hz⟩
      · exact ⟨false, hz⟩) F q
  have hA' : ∀ x, etaleCohomologyPullback jA φA q x =
      (etaleCohomologyPullback (j true) (𝟙 _) q x).comp (Ext.mk₀ φA) (add_zero q) := fun x => by
    rw [etaleCohomologyPullback_comp_mk₀, Category.id_comp]
  have hB' : ∀ x, etaleCohomologyPullback jB φB q x =
      (etaleCohomologyPullback (j false) (𝟙 _) q x).comp (Ext.mk₀ φB) (add_zero q) := fun x => by
    rw [etaleCohomologyPullback_comp_mk₀, Category.id_comp]
  have bA := bijective_comp_mk₀_of_isIso (A := (constantSheaf (smallEtaleTopology A)
    Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) φA q
  have bB := bijective_comp_mk₀_of_isIso (A := (constantSheaf (smallEtaleTopology B)
    Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) φB q
  refine ⟨fun x y hxy => ?_, fun ⟨a, c⟩ => ?_⟩
  · simp only [Prod.mk.injEq, hA', hB'] at hxy
    apply hpi.1
    funext b
    cases b
    · exact bB.1 hxy.2
    · exact bA.1 hxy.1
  · obtain ⟨a', ha'⟩ := bA.2 a
    obtain ⟨c', hc'⟩ := bB.2 c
    obtain ⟨x, hx⟩ := hpi.2 (fun b => match b with
      | true => a'
      | false => c')
    refine ⟨x, ?_⟩
    simp only [Prod.mk.injEq, hA', hB']
    exact ⟨(congrArg (fun z => z.comp (Ext.mk₀ φA) (add_zero q)) (congrFun hx true)).trans ha',
      (congrArg (fun z => z.comp (Ext.mk₀ φB) (add_zero q)) (congrFun hx false)).trans hc'⟩

/-- Pulling back along `a ≫ f` is pulling back along `f` and then along `a`. -/
private theorem etaleCohomologyPullback_eq_comp {W Y Z : Scheme.{u}} (a : W ⟶ Y) (f : Y ⟶ Z)
    (af : W ⟶ Z) (h : af = a ≫ f) (F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} F q) :
    etaleCohomologyPullback af (𝟙 _) q x = etaleCohomologyPullback a
      ((smallEtalePullbackAbComp' a f af h).hom.app F) q (etaleCohomologyPullback f (𝟙 _) q x) := by
  rw [etaleCohomologyPullback_comp a f af h]
  congr 2
  simp

/-- A class vanishing on an open dies along every morphism landing in that open. -/
theorem etaleCohomologyPullback_eq_zero_of_range_subset {T W : Scheme.{u}} (g : W ⟶ T)
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) (V : T.Opens)
    (hg : Set.range g.base ⊆ V) (x : Sheaf.H.{u + 1} G q)
    (hx : etaleCohomologyPullback V.ι (𝟙 ((smallEtalePullbackAb V.ι).obj G)) q x = 0) :
    etaleCohomologyPullback g (𝟙 ((smallEtalePullbackAb g).obj G)) q x = 0 := by
  let l := IsOpenImmersion.lift V.ι g (by rwa [Scheme.Opens.range_ι])
  rw [etaleCohomologyPullback_eq_comp l V.ι g (IsOpenImmersion.lift_fac V.ι g _).symm G q x, hx,
    map_zero]

/-- **Pulling back to a scheme missing a clopen piece forgets the cohomology of that piece.** If
`T` is the disjoint union of opens `V` and `V'` and `g : W ⟶ T` lands in `V'`, a nonzero class on
`V` extends by zero to a nonzero class on `T` killed by pulling back along `g`. -/
theorem not_injective_etaleCohomologyPullback_of_range_subset {T W : Scheme.{u}} (g : W ⟶ T)
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) (V V' : T.Opens) (hdisj : V ⊓ V' = ⊥)
    (hcov : V ⊔ V' = ⊤) (hg : Set.range g.base ⊆ V')
    [Nontrivial (Sheaf.H.{u + 1} ((smallEtalePullbackAb V.ι).obj G) q)] :
    ¬ Function.Injective (etaleCohomologyPullback g (𝟙 ((smallEtalePullbackAb g).obj G)) q) := by
  intro hinj
  have hp := bijective_pullback_pair V.ι V'.ι (disjoint_range_ι_of_inf_eq_bot hdisj)
    (range_ι_union_of_sup_eq_top hcov) G (𝟙 _) (𝟙 _) q
  obtain ⟨a, ha⟩ := exists_ne (0 : Sheaf.H.{u + 1} ((smallEtalePullbackAb V.ι).obj G) q)
  obtain ⟨x, hx⟩ := hp.2 (a, 0)
  simp only [Prod.mk.injEq] at hx
  apply ha
  rw [← hx.1, hinj ((etaleCohomologyPullback_eq_zero_of_range_subset g G q V' hg x hx.2).trans
    (map_zero _).symm), map_zero]

end Pair


/-! ### The kernels of restriction to a family of clopens -/

section Kernels

variable {X : Scheme.{u}} {C : Type*} [CommRing C] (U : Idem C → X.Opens)
  (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (q : ℕ)

/-- Restriction of étale cohomology to the open `U e`. -/
abbrev restrictTo (e : Idem C) :
    Sheaf.H.{u + 1} G q →+ Sheaf.H.{u + 1} ((smallEtalePullbackAb (U e).ι).obj G) q :=
  etaleCohomologyPullback (U e).ι (𝟙 _) q

/-- The classes vanishing on `U e`. -/
abbrev restrictKer (e : Idem C) : AddSubgroup (Sheaf.H.{u + 1} G q) :=
  (restrictTo U G q e).ker

variable {U}

/-- Restriction to a smaller open factors through restriction to a larger one. -/
theorem restrictTo_eq_comp {e f : Idem C} (h : U e ≤ U f) (x : Sheaf.H.{u + 1} G q) :
    restrictTo U G q e x = etaleCohomologyPullback (X.homOfLE h)
      ((smallEtalePullbackAbComp' (X.homOfLE h) (U f).ι (U e).ι
        (Scheme.homOfLE_ι X h).symm).hom.app G) q (restrictTo U G q f x) := by
  exact etaleCohomologyPullback_eq_comp (X.homOfLE h) (U f).ι (U e).ι
    (Scheme.homOfLE_ι X h).symm G q x

/-- On the empty open, étale cohomology vanishes. -/
theorem subsingleton_sheafH_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z]
    (F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} F q) := by
  have h := bijective_etaleCohomologyPullback_pi (ι := Empty) (U := fun _ => Z)
    (fun e => e.elim) (fun a => a.elim) (by
      ext z
      exact (IsEmpty.false z).elim) F q
  exact ⟨fun x y => h.1 (funext fun e => e.elim)⟩

variable (hmono : Monotone U) (hbot : U ⊥ = ⊥) (htop : U ⊤ = ⊤)
  (hdisj : ∀ e f : Idem C, Disjoint e f → U e ⊓ U f = ⊥)
  (hsup : ∀ e f : Idem C, Disjoint e f → U (e ⊔ f) = U e ⊔ U f)

include hmono in
/-- For a monotone family of opens `U`, the classes vanishing on `U e` form an antitone family of
subgroups. -/
theorem restrictKer_antitone : Antitone (restrictKer U G q) := by
  intro e f h x hx
  rw [AddMonoidHom.mem_ker] at hx ⊢
  rw [restrictTo_eq_comp G q (hmono h), hx, map_zero]

include hmono hbot htop hdisj hsup in
/-- **The kernels of restriction to a family of clopens form an additive family.** -/
theorem isAdditiveKernels_restrictKer : IsAdditiveKernels (restrictKer U G q) where
  antitone := restrictKer_antitone G q hmono
  bot := by
    have hempty : ∀ V : X.Opens, V = ⊥ → ∀ w : V, False := by
      rintro V rfl ⟨w, hw⟩
      exact hw
    have : IsEmpty (U ⊥).toScheme := ⟨fun z => hempty _ hbot z⟩
    have := subsingleton_sheafH_of_isEmpty ((smallEtalePullbackAb (U ⊥).ι).obj G) q
    ext x
    simp only [AddSubgroup.mem_top, iff_true, AddMonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  inf_le := by
    intro e f hef x hx
    rw [AddSubgroup.mem_inf] at hx
    obtain ⟨hxe, hxf⟩ := hx
    rw [AddMonoidHom.mem_ker] at hxe hxf ⊢
    have hle : ∀ g, g ≤ e ⊔ f → U g ≤ U (e ⊔ f) := fun g hg => hmono hg
    have hp := bijective_pullback_pair (X.homOfLE (hle e le_sup_left))
      (X.homOfLE (hle f le_sup_right))
      (by
        rw [range_homOfLE, range_homOfLE, Set.disjoint_iff_inter_eq_empty, ← Set.preimage_inter]
        have h := congrArg (fun V : X.Opens => (V : Set X)) (hdisj e f hef)
        simp only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot] at h
        rw [h, Set.preimage_empty])
      (by
        rw [range_homOfLE, range_homOfLE, ← Set.preimage_union]
        have h := congrArg (fun V : X.Opens => (V : Set X)) (hsup e f hef)
        simp only [TopologicalSpace.Opens.coe_sup] at h
        rw [← h]
        ext z
        simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_univ, iff_true]
        exact z.2) ((smallEtalePullbackAb (U (e ⊔ f)).ι).obj G)
      ((smallEtalePullbackAbComp' (X.homOfLE (hle e le_sup_left)) (U (e ⊔ f)).ι (U e).ι
        (Scheme.homOfLE_ι X _).symm).hom.app G)
      ((smallEtalePullbackAbComp' (X.homOfLE (hle f le_sup_right)) (U (e ⊔ f)).ι (U f).ι
        (Scheme.homOfLE_ι X _).symm).hom.app G) q
    apply hp.1
    simp only [map_zero]
    rw [← restrictTo_eq_comp, ← restrictTo_eq_comp, hxe, hxf]
  exists_sub_mem := by
    intro e f hef x y
    have hc : Disjoint e eᶜ := disjoint_compl_right
    have hp := bijective_pullback_pair (U e).ι (U eᶜ).ι
      (disjoint_range_ι_of_inf_eq_bot (hdisj e eᶜ hc))
      (range_ι_union_of_sup_eq_top (by rw [← hsup e eᶜ hc, sup_compl_eq_top, htop]))
      G (𝟙 _) (𝟙 _) q
    obtain ⟨z, hz⟩ := hp.2 (restrictTo U G q e x, restrictTo U G q eᶜ y)
    simp only [Prod.mk.injEq] at hz
    have hf : f ≤ eᶜ := hef.symm.le_compl_right
    refine ⟨z, ?_, ?_⟩
    · rw [AddMonoidHom.mem_ker, map_sub, hz.1, sub_self]
    · rw [AddMonoidHom.mem_ker, map_sub, restrictTo_eq_comp G q (hmono hf) z,
        restrictTo_eq_comp G q (hmono hf) y, hz.2, sub_self]

omit hmono hbot htop hdisj hsup in
include htop in
/-- If `U ⊤ = ⊤`, the only class vanishing on `U ⊤` is zero. -/
theorem restrictKer_top : restrictKer U G q ⊤ = ⊥ := by
  have h := bijective_etaleCohomologyPullback_pi (ι := Unit) (fun _ => (U ⊤).ι)
    (fun a b hab => absurd (Subsingleton.elim a b) hab)
    (by
      rw [Set.iUnion_const, Scheme.Opens.range_ι, htop]
      rfl) G q
  rw [eq_bot_iff]
  intro x hx
  rw [AddMonoidHom.mem_ker] at hx
  rw [AddSubgroup.mem_bot]
  exact h.1 (funext fun _ => hx.trans (map_zero _).symm)

end Kernels

/-! ### Clopens cut out by idempotents, and their preimages -/

section Preimage

variable {X Y : Scheme.{u}} {C : Type*} [CommRing C] (π : Y ⟶ X) {U : Idem C → X.Opens}
  (hmono : Monotone U) (hbot : U ⊥ = ⊥) (htop : U ⊤ = ⊤)
  (hdisj : ∀ e f : Idem C, Disjoint e f → U e ⊓ U f = ⊥)
  (hsup : ∀ e f : Idem C, Disjoint e f → U (e ⊔ f) = U e ⊔ U f)

include hmono in
/-- The preimages under `π` of a monotone family of opens form a monotone family. -/
theorem monotone_preimage : Monotone fun e => π ⁻¹ᵁ U e :=
  fun _ _ h => Scheme.Hom.preimage_mono π (hmono h)

include hbot in
/-- If `U ⊥ = ⊥`, the preimage of `U ⊥` under `π` is empty. -/
theorem preimage_bot : π ⁻¹ᵁ U ⊥ = ⊥ := by
  rw [hbot]
  rfl

include htop in
/-- If `U ⊤ = ⊤`, the preimage of `U ⊤` under `π` is all of `Y`. -/
theorem preimage_top : π ⁻¹ᵁ U ⊤ = ⊤ := by
  rw [htop]
  rfl

include hdisj in
/-- If `U` sends disjoint idempotents to disjoint opens, the preimages under `π` of `U e` and `U f`
are disjoint for disjoint `e` and `f`. -/
theorem preimage_inf (e f : Idem C) (h : Disjoint e f) : π ⁻¹ᵁ U e ⊓ π ⁻¹ᵁ U f = ⊥ :=
  congrArg (fun V => π ⁻¹ᵁ V) (hdisj e f h)

include hsup in
/-- If `U` sends the join of disjoint idempotents to the union of their opens, so does the family
of preimages under `π`. -/
theorem preimage_sup (e f : Idem C) (h : Disjoint e f) :
    π ⁻¹ᵁ U (e ⊔ f) = π ⁻¹ᵁ U e ⊔ π ⁻¹ᵁ U f := by
  rw [hsup e f h]
  rfl

end Preimage

/-! ### Gluing along a morphism -/

section Morphism

variable {T Y : Scheme.{u}} (π : Y ⟶ T) (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ)

/-- Restricting the pullback of a class along `π` to the preimage of an open `V` is pulling back
its restriction to `V` along the restriction of `π`. -/
theorem restrictTo_preimage (V : T.Opens) (x : Sheaf.H.{u + 1} G q) :
    etaleCohomologyPullback (π ⁻¹ᵁ V).ι (𝟙 _) q (etaleCohomologyPullback π (𝟙 _) q x) =
      etaleCohomologyPullback (π ∣_ V)
        ((smallEtalePullbackAbComp' (π ∣_ V) V.ι ((π ⁻¹ᵁ V).ι ≫ π)
          (morphismRestrict_ι π V).symm).hom.app G ≫
          (smallEtalePullbackAbComp' (π ⁻¹ᵁ V).ι π ((π ⁻¹ᵁ V).ι ≫ π) rfl).inv.app G) q
        (etaleCohomologyPullback V.ι (𝟙 _) q x) :=
  etaleCohomologyPullback_square (π ⁻¹ᵁ V).ι π (π ∣_ V) V.ι (morphismRestrict_ι π V).symm G q x

/-- **Gluing restriction maps over the clopens cut out by idempotents.** Let `π : Y ⟶ T` and
let `U` be a family of opens of `T` indexed by the idempotents of a ring, behaving like the
clopens `D(e)`. Pulling back `H^q(T, G) → H^q(Y, π⁻¹G)` is bijective if and only if it is
bijective on the germs at every prime, given any description of these germs as quotients by the
classes vanishing on some `U e`, `e ∉ P`, compatible with pulling back. -/
theorem bijective_etaleCohomologyPullback_iff_germ {C : Type*} [CommRing C]
    {U : Idem C → T.Opens} (hmono : Monotone U) (hbot : U ⊥ = ⊥) (htop : U ⊤ = ⊤)
    (hdisj : ∀ e f : Idem C, Disjoint e f → U e ⊓ U f = ⊥)
    (hsup : ∀ e f : Idem C, Disjoint e f → U (e ⊔ f) = U e ⊔ U f)
    (Hp : ∀ P : Ideal C, P.IsPrime → Type*) [∀ P hP, AddCommGroup (Hp P hP)]
    (Hp' : ∀ P : Ideal C, P.IsPrime → Type*) [∀ P hP, AddCommGroup (Hp' P hP)]
    (germ : ∀ P hP, Sheaf.H.{u + 1} G q →+ Hp P hP)
    (germ' : ∀ P hP, Sheaf.H.{u + 1} ((smallEtalePullbackAb π).obj G) q →+ Hp' P hP)
    (hgerm : ∀ P hP, Function.Surjective (germ P hP))
    (hgerm' : ∀ P hP, Function.Surjective (germ' P hP))
    (hker : ∀ P hP x, germ P hP x = 0 ↔
      ∃ e : Idem C, (e : C) ∉ P ∧ etaleCohomologyPullback (U e).ι (𝟙 _) q x = 0)
    (hker' : ∀ P hP x, germ' P hP x = 0 ↔
      ∃ e : Idem C, (e : C) ∉ P ∧ etaleCohomologyPullback (π ⁻¹ᵁ U e).ι (𝟙 _) q x = 0)
    (ρp : ∀ P hP, Hp P hP →+ Hp' P hP)
    (hρp : ∀ P hP x, ρp P hP (germ P hP x) = germ' P hP (etaleCohomologyPullback π (𝟙 _) q x)) :
    Function.Bijective (etaleCohomologyPullback π (𝟙 ((smallEtalePullbackAb π).obj G)) q) ↔
      ∀ P hP, Function.Bijective (ρp P hP) :=
  bijective_iff_forall_bijective_germ
    (isAdditiveKernels_restrictKer G q hmono hbot htop hdisj hsup)
    (isAdditiveKernels_restrictKer ((smallEtalePullbackAb π).obj G) q (monotone_preimage π hmono)
      (preimage_bot π hbot) (preimage_top π htop) (preimage_inf π hdisj) (preimage_sup π hsup))
    (etaleCohomologyPullback π (𝟙 _) q)
    (fun e x hx => by
      rw [AddMonoidHom.mem_ker] at hx ⊢
      rw [restrictTo, restrictTo_preimage, hx, map_zero])
    (restrictKer_top G q htop) (restrictKer_top _ q (preimage_top π htop))
    Hp Hp' germ germ' hgerm hgerm' hker hker' ρp hρp

/-- **Gluing restriction maps over the clopens cut out by idempotents, at points.** Let
`π : Y ⟶ T`, let `U` be a family of opens of `T` indexed by the idempotents of a ring and behaving
like the clopens `D(e)`, and let `t_P` be a point of `T` for every prime `P`, lying in `U e` for
every `e ∉ P`. Suppose that the cohomology at `t_P`, and at its fibre `Y ×_T t_P`, is the colimit
of the cohomology of the `U e` and of the `π⁻¹ U e`, `e ∉ P`: pulling back is surjective, and a
class dying at the point dies on some `U e`. Then pulling back along `π` is bijective if and only
if pulling back to the fibres over all the points `t_P` is. -/
theorem bijective_etaleCohomologyPullback_iff_points {C : Type*} [CommRing C]
    {U : Idem C → T.Opens} (hmono : Monotone U) (hbot : U ⊥ = ⊥) (htop : U ⊤ = ⊤)
    (hdisj : ∀ e f : Idem C, Disjoint e f → U e ⊓ U f = ⊥)
    (hsup : ∀ e f : Idem C, Disjoint e f → U (e ⊔ f) = U e ⊔ U f)
    {Pt : ∀ P : Ideal C, P.IsPrime → Scheme.{u}} (t : ∀ P hP, Pt P hP ⟶ T)
    (ht : ∀ P hP (e : Idem C), (e : C) ∉ P → Set.range (t P hP).base ⊆ U e)
    (hsurj : ∀ P hP, Function.Surjective
      (etaleCohomologyPullback (t P hP) (𝟙 ((smallEtalePullbackAb (t P hP)).obj G)) q))
    (hloc : ∀ P hP x,
      etaleCohomologyPullback (t P hP) (𝟙 ((smallEtalePullbackAb (t P hP)).obj G)) q x = 0 →
        ∃ e : Idem C, (e : C) ∉ P ∧ etaleCohomologyPullback (U e).ι (𝟙 _) q x = 0)
    (hsurj' : ∀ P hP, Function.Surjective
      (etaleCohomologyPullback (pullback.fst π (t P hP))
        (𝟙 ((smallEtalePullbackAb (pullback.fst π (t P hP))).obj
          ((smallEtalePullbackAb π).obj G))) q))
    (hloc' : ∀ P hP x,
      etaleCohomologyPullback (pullback.fst π (t P hP))
        (𝟙 ((smallEtalePullbackAb (pullback.fst π (t P hP))).obj
          ((smallEtalePullbackAb π).obj G))) q x = 0 →
        ∃ e : Idem C, (e : C) ∉ P ∧ etaleCohomologyPullback (π ⁻¹ᵁ U e).ι (𝟙 _) q x = 0) :
    Function.Bijective (etaleCohomologyPullback π (𝟙 ((smallEtalePullbackAb π).obj G)) q) ↔
      ∀ P hP, Function.Bijective (etaleCohomologyPullback (pullback.snd π (t P hP))
        (𝟙 ((smallEtalePullbackAb (pullback.snd π (t P hP))).obj
          ((smallEtalePullbackAb (t P hP)).obj G))) q) := by
  rw [bijective_etaleCohomologyPullback_iff_germ π G q hmono hbot htop hdisj hsup
    (fun P hP => Sheaf.H.{u + 1} ((smallEtalePullbackAb (t P hP)).obj G) q)
    (fun P hP => Sheaf.H.{u + 1} ((smallEtalePullbackAb (pullback.fst π (t P hP))).obj
      ((smallEtalePullbackAb π).obj G)) q)
    (fun P hP => etaleCohomologyPullback (t P hP) (𝟙 _) q)
    (fun P hP => etaleCohomologyPullback (pullback.fst π (t P hP)) (𝟙 _) q) hsurj hsurj'
    (fun P hP x => ⟨hloc P hP x, fun ⟨e, he, hx⟩ =>
      etaleCohomologyPullback_eq_zero_of_range_subset (t P hP) G q (U e) (ht P hP e he) x hx⟩)
    (fun P hP x => ⟨hloc' P hP x, fun ⟨e, he, hx⟩ =>
      etaleCohomologyPullback_eq_zero_of_range_subset (pullback.fst π (t P hP)) _ q (π ⁻¹ᵁ U e)
        (by
          rintro _ ⟨z, rfl⟩
          change π.base ((pullback.fst π (t P hP)).base z) ∈ U e
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
          exact ht P hP e he ⟨_, rfl⟩) x hx⟩)
    (fun P hP => etaleCohomologyPullback (pullback.snd π (t P hP))
      ((smallEtalePullbackAbComp' (pullback.snd π (t P hP)) (t P hP) (pullback.fst π (t P hP) ≫ π)
        pullback.condition).hom.app G ≫
        (smallEtalePullbackAbComp' (pullback.fst π (t P hP)) π (pullback.fst π (t P hP) ≫ π)
          rfl).inv.app G) q)
    (fun P hP x => (etaleCohomologyPullback_square (pullback.fst π (t P hP)) π
      (pullback.snd π (t P hP)) (t P hP) pullback.condition G q x).symm)]
  exact forall₂_congr fun P hP => bijective_etaleCohomologyPullback_iff_of_isIso_sheaf _ _ q

end Morphism

end Stacks.EtaleCohomology.IdempotentGluing
