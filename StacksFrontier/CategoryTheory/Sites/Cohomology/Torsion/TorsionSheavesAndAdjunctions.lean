module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Torsion abelian sheaves, orthogonality and adjoint functors

Let `(C, J)` be a site. An abelian sheaf is *torsion* when each of its sections is locally
annihilated by a positive integer, which is the condition of Stacks 0DD7. Call an abelian sheaf
`G` *torsion free* when multiplication by every positive integer is a monomorphism of `G`.

The torsion abelian sheaves are exactly the left orthogonal of the torsion free ones: an abelian
sheaf `F` is torsion if and only if every morphism from `F` to a torsion free sheaf vanishes. One
direction is a computation on sections. For the other, the locally torsion sections of `F` form
a subsheaf `F_tors`, the cokernel `F / F_tors` is torsion free, and the vanishing of the
projection `F ⟶ F / F_tors` says that every section of `F` is locally torsion.

Two consequences describe how torsion behaves along functors of abelian sheaves.

* A left adjoint `L` carries torsion sheaves to torsion sheaves: its right adjoint preserves
  monomorphisms, hence torsion free sheaves, so `Hom(LF, G) = Hom(F, RG)` vanishes for `F`
  torsion and `G` torsion free.
* A faithful functor `L` which preserves monomorphisms reflects torsion sheaves: it carries a
  torsion free `G` to a torsion free `LG`, so a morphism `F ⟶ G` is killed by `L` when `LF` is
  torsion, hence vanishes.

## Main results

* `Stacks.Torsion.eq_zero_of_torsionSheafProperty`: a morphism from a torsion sheaf to a torsion
  free sheaf vanishes.
* `Stacks.Torsion.torsionSheafProperty_iff_forall_eq_zero`: the characterization of torsion
  sheaves as the left orthogonal of the torsion free ones.
* `Stacks.Torsion.torsionSheafProperty_obj_of_adjunction`: left adjoints preserve torsion.
* `Stacks.Torsion.torsionSheafProperty_of_torsionSheafProperty_obj`: faithful functors which
  preserve monomorphisms reflect torsion.

## References

* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Torsion

universe w w' v u v' u'

section Orthogonality

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A section of an abelian sheaf which vanishes on the members of a covering sieve vanishes. -/
private lemma sheaf_section_eq_zero (F : Sheaf J AddCommGrpCat.{w}) {U : C}
    (x : F.obj.obj (op U)) {R : Sieve U} (hR : R ∈ J U)
    (hx : ∀ ⦃V : C⦄ (f : V ⟶ U), R f → F.obj.map f.op x = 0) : x = 0 := by
  have hF := (isSheaf_iff_isSheaf_of_type J _).mp
    (GrothendieckTopology.HasSheafCompose.isSheaf F.obj F.2
      (F := forget AddCommGrpCat.{w}))
  refine (hF.isSeparated _ hR).ext fun V f hf ↦ ?_
  change F.obj.map f.op x = F.obj.map f.op 0
  exact (hx f hf).trans (map_zero _).symm

/-- Multiples of a morphism of abelian sheaves are computed sectionwise. -/
private lemma sheafHom_nsmul_app_apply {F G : Sheaf J AddCommGrpCat.{w}} (g : F ⟶ G) (n : ℕ)
    {U : Cᵒᵖ} (x : F.obj.obj U) : (n • g).hom.app U x = n • g.hom.app U x := by
  let E := sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
  change (E.map (n • g)) x = n • (E.map g) x
  rw [E.map_nsmul]
  rfl

/-- A morphism of abelian sheaves which is injective on sections is a monomorphism. -/
private lemma mono_of_injective_app {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G)
    (h : ∀ U, Function.Injective (f.hom.app U)) : Mono f := by
  apply (sheafToPresheaf J AddCommGrpCat.{w}).mono_of_mono_map
  have : ∀ U, Mono (((sheafToPresheaf J AddCommGrpCat.{w}).map f).app U) := fun U ↦ by
    rw [AddCommGrpCat.mono_iff_injective]
    exact h U
  exact NatTrans.mono_of_mono_app _

/-- On a torsion free abelian sheaf, multiplication by a positive integer is injective on
sections. -/
private lemma nsmul_injective_of_mono [HasSheafify J AddCommGrpCat.{w}]
    {G : Sheaf J AddCommGrpCat.{w}} {n : ℕ}
    (h : Mono (n • 𝟙 G)) (V : Cᵒᵖ) : Function.Injective (fun y : G.obj.obj V ↦ n • y) := by
  have hi := (AddCommGrpCat.mono_iff_injective ((n • 𝟙 G).hom.app V)).mp inferInstance
  exact fun y z hyz ↦ hi <| by
    simpa only [sheafHom_nsmul_app_apply, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
      AddCommGrpCat.id_apply] using hyz

/-- **A morphism from a torsion abelian sheaf to a torsion free one vanishes.** A section of the
source is annihilated on a covering sieve by positive integers, so is its image, and
multiplication by a positive integer is injective on the target. -/
theorem eq_zero_of_torsionSheafProperty [HasSheafify J AddCommGrpCat.{w}]
    {F G : Sheaf J AddCommGrpCat.{w}}
    (hF : torsionSheafProperty J F) (hG : ∀ n : ℕ, 0 < n → Mono (n • 𝟙 G)) (g : F ⟶ G) :
    g = 0 := by
  ext U x
  change g.hom.app U x = 0
  obtain ⟨R, hR, hx⟩ := hF U.unop x
  refine sheaf_section_eq_zero J G _ hR fun V f hf ↦ ?_
  obtain ⟨n, hn, hnx⟩ := hx V f hf
  apply nsmul_injective_of_mono J (hG n hn) (op V)
  change n • G.obj.map f.op (g.hom.app U x) = n • 0
  rw [← g.hom.naturality_apply f.op, ← _root_.map_nsmul, hnx, map_zero, nsmul_zero]

/-! ### The torsion subsheaf -/

/-- The sections of `F` which are annihilated by a positive integer. -/
private def torsionSectionsSubfunctor (F : Sheaf J AddCommGrpCat.{w}) :
    Subfunctor (F.obj ⋙ forget AddCommGrpCat.{w}) where
  obj U := {x | ∃ n : ℕ, 0 < n ∧ n • x = 0}
  map {U V} f x hx := by
    obtain ⟨n, hn, hnx⟩ := hx
    refine ⟨n, hn, ?_⟩
    change n • (F.obj.map f) x = 0
    rw [← _root_.map_nsmul]
    change (F.obj.map f) (n • x) = 0
    rw [hnx, map_zero]

/-- The sections of `F` which are locally annihilated by a positive integer. -/
private def localTorsionSubfunctor (F : Sheaf J AddCommGrpCat.{w}) :
    Subfunctor (F.obj ⋙ forget AddCommGrpCat.{w}) :=
  (torsionSectionsSubfunctor J F).sheafify J

private lemma mem_localTorsionSubfunctor_iff (F : Sheaf J AddCommGrpCat.{w}) {U : Cᵒᵖ}
    (x : F.obj.obj U) :
    x ∈ (localTorsionSubfunctor J F).obj U ↔
      (torsionSectionsSubfunctor J F).sieveOfSection x ∈ J U.unop :=
  Iff.rfl

/-- The locally torsion sections of `F` over `U` form a subgroup. -/
private def localTorsionAddSubgroup (F : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ) :
    AddSubgroup (F.obj.obj U) where
  carrier := (localTorsionSubfunctor J F).obj U
  zero_mem' := by
    rw [mem_localTorsionSubfunctor_iff]
    refine J.superset_covering (fun V i _ ↦ ⟨1, Nat.one_pos, ?_⟩) (J.top_mem U.unop)
    change 1 • (F.obj.map i.op).hom' (0 : F.obj.obj U) = 0
    rw [(F.obj.map i.op).hom'.map_zero]
    exact one_nsmul (0 : F.obj.obj (op V))
  add_mem' := by
    intro x y hx hy
    rw [mem_localTorsionSubfunctor_iff] at hx hy ⊢
    refine J.superset_covering ?_ (J.intersection_covering hx hy)
    rintro V i ⟨⟨n, hn, hnx⟩, ⟨m, hm, hmy⟩⟩
    change n • (F.obj.map i.op) x = 0 at hnx
    change m • (F.obj.map i.op) y = 0 at hmy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    change (n * m) • (F.obj.map i.op) (x + y) = 0
    rw [map_add, nsmul_add, Nat.mul_comm n m, ← smul_smul, hnx, nsmul_zero, zero_add,
      Nat.mul_comm m n, ← smul_smul, hmy, nsmul_zero]
  neg_mem' := by
    intro x hx
    rw [mem_localTorsionSubfunctor_iff] at hx ⊢
    refine J.superset_covering ?_ hx
    rintro V i ⟨n, hn, hnx⟩
    refine ⟨n, hn, ?_⟩
    change n • (F.obj.map i.op) (-x) = 0
    change n • (F.obj.map i.op) x = 0 at hnx
    rw [map_neg, smul_neg, hnx, neg_zero]

/-- The presheaf of locally torsion sections of `F`. -/
private def localTorsionPresheaf (F : Sheaf J AddCommGrpCat.{w}) : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (localTorsionAddSubgroup J F U)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun x ↦ ⟨F.obj.map i x.val, (localTorsionSubfunctor J F).map i x.property⟩
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  map_id U := by ext x; simp
  map_comp i j := by ext x; simp

/-- The inclusion of the locally torsion sections. -/
private def localTorsionPresheafι (F : Sheaf J AddCommGrpCat.{w}) :
    localTorsionPresheaf J F ⟶ F.obj where
  app U := AddCommGrpCat.ofHom (localTorsionAddSubgroup J F U).subtype
  naturality U V i := by ext; rfl

/-- The torsion subsheaf `F_tors` of `F`: its sections are the locally torsion sections. -/
private def localTorsionSheaf (F : Sheaf J AddCommGrpCat.{w}) : Sheaf J AddCommGrpCat.{w} where
  obj := localTorsionPresheaf J F
  property := by
    apply Presheaf.isSheaf_of_isSheaf_comp J (s := forget AddCommGrpCat.{w})
    rw [isSheaf_iff_isSheaf_of_type]
    change Presieve.IsSheaf J (localTorsionSubfunctor J F).toFunctor
    apply Subfunctor.sheafify_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.HasSheafCompose.isSheaf F.obj F.2

/-- The inclusion `F_tors ⟶ F`. -/
private def localTorsionSheafι (F : Sheaf J AddCommGrpCat.{w}) : localTorsionSheaf J F ⟶ F :=
  ⟨localTorsionPresheafι J F⟩

private lemma mono_localTorsionSheafι (F : Sheaf J AddCommGrpCat.{w}) :
    Mono (localTorsionSheafι J F) :=
  mono_of_injective_app J _ fun _ ↦ Subtype.val_injective

variable [HasSheafify J AddCommGrpCat.{w}]

/-- A section of the cokernel of `F_tors ⟶ F` coming from `F` vanishes exactly when the section
of `F` is locally torsion. -/
private lemma cokernel_localTorsionSheafι_app_eq_zero_iff (F : Sheaf J AddCommGrpCat.{w})
    (U : C) (x : F.obj.obj (op U)) :
    (cokernel.π (localTorsionSheafι J F)).hom.app (op U) x = 0 ↔
      x ∈ (localTorsionSubfunctor J F).obj (op U) := by
  have := mono_localTorsionSheafι J F
  refine ⟨fun hx ↦ ?_, fun hx ↦ ConcreteCategory.congr_hom
    (congr_app (congrArg (fun g ↦ g.hom) (cokernel.condition (localTorsionSheafι J F))) (op U))
    (⟨x, hx⟩ : (localTorsionSheaf J F).obj.obj (op U))⟩
  let Ev := sheafToPresheaf J AddCommGrpCat.{w} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U)
  let T := ShortComplex.mk (localTorsionSheafι J F) (cokernel.π (localTorsionSheafι J F))
    (cokernel.condition _)
  have hf : IsLimit (KernelFork.ofι (localTorsionSheafι J F)
      (cokernel.condition (localTorsionSheafι J F))) :=
    Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)
  obtain ⟨y, hy⟩ := (T.map Ev).ab_exact_iff.mp
    ((T.map Ev).exact_of_f_is_kernel (KernelFork.mapIsLimit _ hf Ev)) x hx
  change y.val = x at hy
  exact hy ▸ y.property

/-- **The cokernel of `F_tors ⟶ F` is torsion free.** If `n • x = 0` for a section `x` of the
cokernel, lift `x` locally to sections `y` of `F`; then `n • y` is locally torsion, hence so is
`y`, and `x` vanishes locally. -/
private lemma mono_nsmul_cokernel_localTorsionSheafι [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (hn : 0 < n) :
    Mono (n • 𝟙 (cokernel (localTorsionSheafι J F))) := by
  let q := cokernel.π (localTorsionSheafι J F)
  have hq : Sheaf.IsLocallySurjective q :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{w} q).mpr inferInstance
  have hzero : ∀ (U : C) (x : (cokernel (localTorsionSheafι J F)).obj.obj (op U)),
      n • x = 0 → x = 0 := by
    intro U x hx
    refine sheaf_section_eq_zero J _ x (hq.imageSieve_mem x) fun V f hf ↦ ?_
    obtain ⟨y, hy⟩ := hf
    rw [← hy]
    apply (cokernel_localTorsionSheafι_app_eq_zero_iff J F V y).mpr
    have hny : n • y ∈ (localTorsionSubfunctor J F).obj (op V) := by
      apply (cokernel_localTorsionSheafι_app_eq_zero_iff J F V (n • y)).mp
      change q.hom.app (op V) (n • y) = 0
      rw [_root_.map_nsmul, hy, ← _root_.map_nsmul, hx, map_zero]
    rw [mem_localTorsionSubfunctor_iff] at hny ⊢
    refine J.superset_covering ?_ hny
    rintro W g ⟨m, hm, hmy⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    change m • (F.obj.map g.op) (n • y) = 0 at hmy
    change (m * n) • F.obj.map g.op y = 0
    simpa only [_root_.map_nsmul, smul_smul] using hmy
  refine mono_of_injective_app J _ fun U ↦ ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine hzero U.unop x ?_
  simpa only [sheafHom_nsmul_app_apply, ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app, AddCommGrpCat.id_apply] using hx

/-- **Torsion sheaves are the left orthogonal of the torsion free sheaves.** An abelian sheaf is
torsion if and only if every morphism from it to a torsion free abelian sheaf vanishes. -/
theorem torsionSheafProperty_iff_forall_eq_zero [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : Sheaf J AddCommGrpCat.{w}) :
    torsionSheafProperty J F ↔
      ∀ (G : Sheaf J AddCommGrpCat.{w}), (∀ n : ℕ, 0 < n → Mono (n • 𝟙 G)) →
        ∀ g : F ⟶ G, g = 0 := by
  refine ⟨fun hF _ hG ↦ eq_zero_of_torsionSheafProperty J hF hG, fun h U x ↦ ?_⟩
  have hx : x ∈ (localTorsionSubfunctor J F).obj (op U) :=
    (cokernel_localTorsionSheafι_app_eq_zero_iff J F U x).mp <| by
      rw [h _ (mono_nsmul_cokernel_localTorsionSheafι J F) (cokernel.π _)]
      rfl
  exact ⟨(torsionSectionsSubfunctor J F).sieveOfSection x, hx, fun V f hf ↦ hf⟩

end Orthogonality

section Functors

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- An additive functor preserving monomorphisms carries a monic `n • 𝟙 X` to a monic
`n • 𝟙 (F.obj X)`. -/
private lemma mono_nsmul_id_obj {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    {X : A} {n : ℕ} (h : Mono (n • 𝟙 X)) : Mono (n • 𝟙 (F.obj X)) := by
  have : Mono (F.map (n • 𝟙 X)) := inferInstance
  rwa [F.map_nsmul, F.map_id] at this

/-- **A left adjoint between categories of abelian sheaves preserves torsion sheaves.** Its right
adjoint preserves monomorphisms, hence torsion free sheaves, so morphisms from `L F` to a torsion
free sheaf correspond to morphisms from `F` to a torsion free sheaf, which vanish. -/
theorem torsionSheafProperty_obj_of_adjunction [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w'}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    {L : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w'}}
    {R : Sheaf K AddCommGrpCat.{w'} ⥤ Sheaf J AddCommGrpCat.{w}} [R.Additive] (adj : L ⊣ R)
    {F : Sheaf J AddCommGrpCat.{w}} (hF : torsionSheafProperty J F) :
    torsionSheafProperty K (L.obj F) := by
  rw [torsionSheafProperty_iff_forall_eq_zero]
  intro G hG g
  have : R.IsRightAdjoint := adj.isRightAdjoint
  apply (adj.homEquiv F G).injective
  rw [eq_zero_of_torsionSheafProperty J hF (fun n hn ↦ mono_nsmul_id_obj R (hG n hn))
    (adj.homEquiv F G g), Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

/-- **A faithful functor between categories of abelian sheaves which preserves monomorphisms
reflects torsion sheaves.** It carries a torsion free sheaf to a torsion free one, so it kills
every morphism from `F` to a torsion free sheaf once `L F` is torsion. -/
theorem torsionSheafProperty_of_torsionSheafProperty_obj [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w'}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (L : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w'}) [L.Additive] [L.Faithful]
    [L.PreservesMonomorphisms] {F : Sheaf J AddCommGrpCat.{w}}
    (hF : torsionSheafProperty K (L.obj F)) : torsionSheafProperty J F :=
  (torsionSheafProperty_iff_forall_eq_zero J F).2 fun _ hG g ↦ L.map_injective <|
    (eq_zero_of_torsionSheafProperty K hF (fun n hn ↦ mono_nsmul_id_obj L (hG n hn))
      (L.map g)).trans (L.map_zero _ _).symm

end Functors

end Stacks.Torsion

end
