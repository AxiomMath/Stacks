module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BoundedCovering
import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheaf

/-!
# Compactly supported sections of a locally constant sheaf on a non-proper scheme

Let `X` be an integral scheme locally of finite type over a field `k` and let `ℱ` be a locally
constant abelian sheaf on the small étale site of `X`. If `X` is not proper over `k`, then the
group of global sections of `ℱ` with support proper over `k` is zero.

## Main results

* `Stacks.EtaleCohomology.map_openObjectι_injective_of_dense` — restriction of a locally
  constant abelian sheaf along a dense open immersion of the small étale site is injective.
* `Stacks.EtaleCohomology.compactlySupportedSections_eq_bot_of_not_isProper` — the group of
  global sections with support proper over the base field vanishes on an integral scheme which
  is not proper over the base field.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
* [Stacks Project, Tag 0F72](https://stacks.math.columbia.edu/tag/0F72)
* [Stacks Project, Tag 04FR](https://stacks.math.columbia.edu/tag/04FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.ConstantSheaf

universe u

namespace Stacks.EtaleCohomology

/-! ### Sheaf theoretic emptiness on the small étale site -/

section Emptiness

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The empty family is not covering over an object of the small étale site with a point. -/
public theorem not_bot_mem_smallEtaleTopology {V : SmallEtale B S hS}
    (x : (SmallEtale.toScheme B S hS).obj V) :
    (⊥ : Sieve V) ∉ SmallEtale.topology B S hS V := by
  intro hbot
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1
    (locallyConstantMaps_isSheaf_smallEtale.{u, 0} B S hS
      (ULift.{u + 1, 0} (Multiplicative (ZMod 2))))
  have key : ∀ a b : LocallyConstant ((SmallEtale.toScheme B S hS).obj V)
      (ULift.{u + 1, 0} (Multiplicative (ZMod 2))), a = b :=
    fun _ _ => (hsheaf ⊥ hbot).isSeparatedFor.ext fun _ _ hg => hg.elim
  have h2 := congrArg (fun g => g x)
    (key (LocallyConstant.const _ (ULift.up (1 : Multiplicative (ZMod 2))))
      (LocallyConstant.const _ (ULift.up (Multiplicative.ofAdd (1 : ZMod 2)))))
  simp only [LocallyConstant.coe_const, Function.const_apply, ULift.up.injEq] at h2
  exact absurd h2 (by decide)

/-- An object of the small étale site over which the empty family is not covering has a
point. -/
public theorem nonempty_of_not_bot_mem_smallEtaleTopology {V : SmallEtale B S hS}
    (h : (⊥ : Sieve V) ∉ SmallEtale.topology B S hS V) :
    Nonempty ((SmallEtale.toScheme B S hS).obj V) :=
  not_isEmpty_iff.mp fun hV => h (bot_mem_topology B hS hV)

/-- The empty family is covering over an object of a slice of the small étale site exactly when
it is covering over the underlying object. -/
public theorem bot_mem_over_iff (Y : SmallEtale B S hS) (T : Over Y) :
    (⊥ : Sieve T) ∈ (SmallEtale.topology B S hS).over Y T ↔
      (⊥ : Sieve T.left) ∈ SmallEtale.topology B S hS T.left := by
  rw [GrothendieckTopology.mem_over_iff, OrderIso.map_bot]

end Emptiness

/-! ### Restriction of a constant sheaf -/

/-- A commuting square in the source category gives a commuting square of restriction maps. -/
private theorem map_op_apply_eq_of_comp_eq {C : Type*} [Category C]
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1}) {A B D T : C} (f : A ⟶ B) (g : B ⟶ T) (f' : A ⟶ D)
    (g' : D ⟶ T) (h : f ≫ g = f' ≫ g') (z : ToType (H.obj (op T))) :
    ConcreteCategory.hom (H.map f.op) (ConcreteCategory.hom (H.map g.op) z) =
      ConcreteCategory.hom (H.map f'.op) (ConcreteCategory.hom (H.map g'.op) z) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← H.map_comp,
    ← H.map_comp, ← op_comp, ← op_comp, h]

/-- **A sheaf which is locally the constant presheaf has injective restriction along a morphism
which is dense in the sheaf theoretic sense.** The density hypothesis is that every object over
the target which is not sheaf theoretically empty is refined, compatibly, by an object over the
source which is not sheaf theoretically empty either. -/
private theorem constantComparison_map_injective {C : Type (u + 1)} [Category.{u} C]
    (K : GrothendieckTopology C) (E : AddCommGrpCat.{u + 1})
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hH : Presieve.IsSheaf K (H ⋙ forget AddCommGrpCat.{u + 1}))
    (η : (Functor.const Cᵒᵖ).obj E ⟶ H)
    [Presheaf.IsLocallyInjective K η] [Presheaf.IsLocallySurjective K η]
    {T W : C} (m : W ⟶ T)
    (hm : ∀ (Y : C) (l : Y ⟶ T), (⊥ : Sieve Y) ∉ K Y →
      ∃ (Q : C) (q : Q ⟶ Y) (r : Q ⟶ W), q ≫ l = r ≫ m ∧ (⊥ : Sieve Q) ∉ K Q) :
    Function.Injective (ConcreteCategory.hom (H.map m.op)) := by
  intro x y hxy
  have hcov : Presheaf.imageSieve η x ⊓ Presheaf.imageSieve η y ∈ K T :=
    K.intersection_covering (Presheaf.imageSieve_mem K η x) (Presheaf.imageSieve_mem K η y)
  refine (hH _ hcov).isSeparatedFor.ext ?_
  intro Y l hl
  obtain ⟨xv, hxv⟩ := hl.1
  obtain ⟨yv, hyv⟩ := hl.2
  by_cases hY : (⊥ : Sieve Y) ∈ K Y
  · exact (hH ⊥ hY).isSeparatedFor.ext fun _ _ hg => hg.elim
  obtain ⟨Q, q, r, hcomm, hQ⟩ := hm Y l hY
  have hnat : ∀ v : E, ConcreteCategory.hom (η.app (op Q)) v =
      ConcreteCategory.hom (H.map q.op) (ConcreteCategory.hom (η.app (op Y)) v) :=
    fun v => NatTrans.naturality_apply η q.op v
  have hval : ConcreteCategory.hom (η.app (op Q)) xv =
      ConcreteCategory.hom (η.app (op Q)) yv := by
    rw [hnat xv, hnat yv, hxv, hyv, map_op_apply_eq_of_comp_eq H q l r m hcomm,
      map_op_apply_eq_of_comp_eq H q l r m hcomm, hxy]
  have hsieve := Presheaf.equalizerSieve_mem K η (X := op Q) xv yv hval
  have hvv : xv = yv := by
    by_contra hne
    refine hQ ?_
    have hle : Presheaf.equalizerSieve (F := (Functor.const Cᵒᵖ).obj E)
        (X := op Q) xv yv ≤ ⊥ := fun Z g hg => absurd hg hne
    rwa [le_bot_iff.mp hle] at hsieve
  exact (hxv.symm.trans (hvv ▸ rfl)).trans hyv

/-- **Restriction of a constant abelian sheaf is injective along a morphism which is dense in
the sheaf theoretic sense.** The density hypothesis is that every object over the target which
is not sheaf theoretically empty is refined, compatibly, by an object over the source which is
not sheaf theoretically empty either. -/
public theorem constantSheaf_map_injective {C : Type (u + 1)} [Category.{u} C]
    (K : GrothendieckTopology C) [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [K.HasSheafCompose (forget AddCommGrpCat.{u + 1})]
    (E : AddCommGrpCat.{u + 1}) {T W : C} (m : W ⟶ T)
    (hm : ∀ (Y : C) (l : Y ⟶ T), (⊥ : Sieve Y) ∉ K Y →
      ∃ (Q : C) (q : Q ⟶ Y) (r : Q ⟶ W), q ≫ l = r ≫ m ∧ (⊥ : Sieve Q) ∉ K Q) :
    Function.Injective (ConcreteCategory.hom
      (((constantSheaf K AddCommGrpCat.{u + 1}).obj E).obj.map m.op)) := by
  refine constantComparison_map_injective K E
    (sheafify K ((Functor.const Cᵒᵖ).obj E)) ?_
    (toSheafify K ((Functor.const Cᵒᵖ).obj E)) m hm
  exact (isSheaf_iff_isSheaf_of_type K _).1
    (GrothendieckTopology.HasSheafCompose.isSheaf _
      ((presheafToSheaf K AddCommGrpCat.{u + 1}).obj ((Functor.const Cᵒᵖ).obj E)).property)

/-! ### Restriction along a dense open immersion -/

section Dense

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inclusion of a Zariski open of an object of the small étale site, as a morphism of the
slice site over that object into its terminal object. -/
public def overOpenObjectHom (Y : SmallEtale B S hS)
    (O : ((SmallEtale.toScheme B S hS).obj Y).Opens) :
    Over.mk (openObjectι B S hS Y O) ⟶ Over.mk (𝟙 Y) :=
  Over.homMk (openObjectι B S hS Y O) (Category.comp_id _)

/-- The inclusion of the preimage of a Zariski open, followed by the morphism along which the
preimage is taken, has image inside that open. -/
private theorem range_openObjectι_comp_subset {Z U : SmallEtale B S hS} (g : Z ⟶ U)
    (O : ((SmallEtale.toScheme B S hS).obj U).Opens) :
    Set.range ((SmallEtale.toScheme B S hS).map
        (openObjectι B S hS Z ((SmallEtale.toScheme B S hS).map g ⁻¹ᵁ O) ≫ g)).base
      ⊆ (O : Set ((SmallEtale.toScheme B S hS).obj U)) := by
  rintro z ⟨w, rfl⟩
  have hmem : ((SmallEtale.toScheme B S hS).map
        (openObjectι B S hS Z ((SmallEtale.toScheme B S hS).map g ⁻¹ᵁ O))).base w
      ∈ Set.range ((SmallEtale.toScheme B S hS).map
        (openObjectι B S hS Z ((SmallEtale.toScheme B S hS).map g ⁻¹ᵁ O))).base :=
    Set.mem_range_self w
  rw [openObjectι_range] at hmem
  simp only [Functor.map_comp, Scheme.Hom.comp_apply]
  exact hmem

/-- The preimage of a dense open under a morphism of the small étale site is dense. -/
private theorem dense_preimage_opens {Z U : SmallEtale B S hS} (g : Z ⟶ U)
    {O : ((SmallEtale.toScheme B S hS).obj U).Opens}
    (hO : Dense (O : Set ((SmallEtale.toScheme B S hS).obj U))) :
    Dense (((SmallEtale.toScheme B S hS).map g ⁻¹ᵁ O :
      ((SmallEtale.toScheme B S hS).obj Z).Opens) : Set ((SmallEtale.toScheme B S hS).obj Z)) :=
  hO.preimage ((SmallEtale.toScheme B S hS).map g).isOpenMap

/-- **Restriction of a constant abelian sheaf on a slice of the small étale site along a dense
open immersion is injective.** -/
public theorem isConstant_map_overOpenObjectHom_injective (Y : SmallEtale B S hS)
    (G : Sheaf ((SmallEtale.topology B S hS).over Y) AddCommGrpCat.{u + 1})
    [Sheaf.IsConstant ((SmallEtale.topology B S hS).over Y) G]
    (O : ((SmallEtale.toScheme B S hS).obj Y).Opens)
    (hO : Dense (O : Set ((SmallEtale.toScheme B S hS).obj Y))) :
    Function.Injective (ConcreteCategory.hom
      (G.obj.map (overOpenObjectHom B S hS Y O).op)) := by
  obtain ⟨E, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant
    ((SmallEtale.topology B S hS).over Y) G
  have hconst := constantSheaf_map_injective
    ((SmallEtale.topology B S hS).over Y) E (overOpenObjectHom B S hS Y O) ?_
  · intro x y hxy
    have hstep : ConcreteCategory.hom
          (((constantSheaf ((SmallEtale.topology B S hS).over Y)
            AddCommGrpCat.{u + 1}).obj E).obj.map (overOpenObjectHom B S hS Y O).op)
          (ConcreteCategory.hom (e.inv.hom.app (op (Over.mk (𝟙 Y)))) x) =
        ConcreteCategory.hom
          (((constantSheaf ((SmallEtale.topology B S hS).over Y)
            AddCommGrpCat.{u + 1}).obj E).obj.map (overOpenObjectHom B S hS Y O).op)
          (ConcreteCategory.hom (e.inv.hom.app (op (Over.mk (𝟙 Y)))) y) := by
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← e.inv.hom.naturality, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hxy]
    exact (ConcreteCategory.bijective_of_isIso
      (e.inv.hom.app (op (Over.mk (𝟙 Y))))).1 (hconst hstep)
  · intro Z l hZ
    have hZne : Nonempty ((SmallEtale.toScheme B S hS).obj Z.left) :=
      nonempty_of_not_bot_mem_smallEtaleTopology B S hS
        (fun hb => hZ ((bot_mem_over_iff B S hS Y Z).2 hb))
    have hO'dense := dense_preimage_opens B S hS Z.hom hO
    refine ⟨Over.mk (openObjectι B S hS Z.left
        ((SmallEtale.toScheme B S hS).map Z.hom ⁻¹ᵁ O) ≫ Z.hom),
      Over.homMk (openObjectι B S hS Z.left
        ((SmallEtale.toScheme B S hS).map Z.hom ⁻¹ᵁ O)) rfl,
      Over.homMk (factorThroughOpenObject B S hS _ Y _ O
        (range_openObjectι_comp_subset B S hS Z.hom O))
        (factorThroughOpenObject_fac B S hS _ Y _ O
          (range_openObjectι_comp_subset B S hS Z.hom O)),
      Over.mkIdTerminal.hom_ext _ _, ?_⟩
    obtain ⟨z, hz⟩ := hO'dense.nonempty
    rw [← openObjectι_range B S hS Z.left
      ((SmallEtale.toScheme B S hS).map Z.hom ⁻¹ᵁ O)] at hz
    obtain ⟨w, -⟩ := hz
    exact fun hb => not_bot_mem_smallEtaleTopology B S hS w
      ((bot_mem_over_iff B S hS Y _).1 hb)

/-- **Restriction of a locally constant abelian sheaf on the small étale site along a dense
open immersion is injective.** -/
public theorem map_openObjectι_injective_of_dense
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1})
    [hF : IsLocallyConstant (SmallEtale.topology B S hS) F]
    (U : SmallEtale B S hS) (O : ((SmallEtale.toScheme B S hS).obj U).Opens)
    (hO : Dense (O : Set ((SmallEtale.toScheme B S hS).obj U))) :
    Function.Injective (ConcreteCategory.hom
      (F.obj.map (openObjectι B S hS U O).op)) := by
  intro s t hst
  obtain ⟨I, Yc, p, hcover, hpconst⟩ := hF.exists_cover U
  have hsheaf : Presieve.IsSheaf (SmallEtale.topology B S hS)
      (F.obj ⋙ forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf F.obj F.property)
  refine (hsheaf _ hcover).isSeparatedFor.ext ?_
  rintro Z l ⟨V, a, b, ⟨i⟩, rfl⟩
  have hkey : ConcreteCategory.hom (F.obj.map (p i).op) s =
      ConcreteCategory.hom (F.obj.map (p i).op) t := by
    have hO'dense := dense_preimage_opens B S hS (p i) hO
    have hinj := isConstant_map_overOpenObjectHom_injective B S hS (Yc i)
      (((SmallEtale.topology B S hS).overPullback AddCommGrpCat.{u + 1} (Yc i)).obj F) _ hO'dense
    refine hinj ?_
    have hfac := factorThroughOpenObject_fac B S hS _ U _ O
      (range_openObjectι_comp_subset B S hS (p i) O)
    have hmove := fun z => map_op_apply_eq_of_comp_eq F.obj _ _ _ _ hfac.symm z
    exact (hmove s).trans ((congrArg _ hst).trans (hmove t).symm)
  have hfinal : ConcreteCategory.hom (F.obj.map ((p i).op ≫ a.op)) s =
      ConcreteCategory.hom (F.obj.map ((p i).op ≫ a.op)) t := by
    rw [F.obj.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hkey]
  exact hfinal

end Dense

/-! ### Vanishing of the sections with proper support -/

/-- A closed subset proper over the base which is the whole scheme makes a reduced scheme
proper over the base. -/
public theorem isProper_of_isProperOver_top {X T : Scheme.{u}} [IsReduced X] (f : X ⟶ T)
    [LocallyOfFiniteType f] (h : IsProperOver f ⊤) : IsProper f := by
  change IsProper ((Scheme.IdealSheafData.vanishingIdeal ⊤).subschemeι ≫ f) at h
  rw [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot] at h
  set j := (⊥ : X.IdealSheafData).subschemeι
  have hjf : IsProper (j ≫ f) := h
  simpa using (inferInstance : IsProper (inv j ≫ (j ≫ f)))

section Vanishing

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] (B : BigEtaleSite.{u}) (hX : B.Contains X)
  (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})

/-- On an irreducible scheme a global section of a locally constant abelian sheaf with a
nonempty zero locus vanishes. -/
public theorem eq_zero_of_zeroOpen_ne_bot [IrreducibleSpace X]
    [IsLocallyConstant (SmallEtale.topology B X hX) F]
    (s : ToType (F.obj.obj (op (SmallEtale.final B X hX))))
    (h : zeroOpen B X hX F (SmallEtale.final B X hX) s ≠ ⊥) : s = 0 := by
  have hpre : PreirreducibleSpace ((SmallEtale.toScheme B X hX).obj
      (SmallEtale.final B X hX)) := inferInstanceAs (PreirreducibleSpace X)
  have hne : ((zeroOpen B X hX F (SmallEtale.final B X hX) s :
      ((SmallEtale.toScheme B X hX).obj (SmallEtale.final B X hX)).Opens) :
        Set ((SmallEtale.toScheme B X hX).obj (SmallEtale.final B X hX))).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun he => h (TopologicalSpace.Opens.ext he)
  have hzero : ConcreteCategory.hom (F.obj.map (openObjectι B X hX (SmallEtale.final B X hX)
      (zeroOpen B X hX F (SmallEtale.final B X hX) s)).op) s = 0 := by
    refine (map_eq_zero_iff_le_zeroOpen B X hX F _ s _
      (openObjectι B X hX (SmallEtale.final B X hX)
        (zeroOpen B X hX F (SmallEtale.final B X hX) s))).2 ?_
    rw [openObjectι_opensRange]
  refine map_openObjectι_injective_of_dense B X hX F _ _
    ((zeroOpen B X hX F (SmallEtale.final B X hX) s).isOpen.dense hne) ?_
  rw [hzero, map_zero]

/-- On an integral scheme which is not proper over the base field, a global section of a locally
constant abelian sheaf on the small étale site whose support is proper over the base field is
zero. -/
@[stacks 03VL "the non-projective assertion H^0_c = 0, at the level of the sections of proper \
support of Tag 0F72: for an arbitrary locally constant abelian sheaf in place of the sheaf \
ℱ_ρ attached to a representation, which needs part (1) of Tag 0DV5 and hence Tag 0245, and \
on an integral scheme not proper over the base field in place of a non-projective \
geometrically connected smooth curve. The identification of these sections with H^0_c is Tag \
0GK1, not available here; the two projective assertions of the tag are not proved, nor is the \
Tate twist they carry", sga "4½ Sommes_trig 1.18" "Clause b)"]
public theorem compactlySupportedSections_eq_bot_of_not_isProper [IsIntegral X]
    (hf : ¬ IsProper f) [IsLocallyConstant (SmallEtale.topology B X hX) F] :
    compactlySupportedSections k X f B hX F = ⊥ := by
  refine le_antisymm (fun s hs => ?_) bot_le
  rw [AddSubgroup.mem_bot]
  by_contra hne
  have hbot : zeroOpen B X hX F (SmallEtale.final B X hX) s = ⊥ := by
    by_contra hcon
    exact hne (eq_zero_of_zeroOpen_ne_bot B hX F s hcon)
  have hp : IsProperOver f (zeroOpen B X hX F (SmallEtale.final B X hX) s).compl :=
    (mem_compactlySupportedSections k X f B hX F s).1 hs
  refine hf (isProper_of_isProperOver_top f (isProperOver_of_le f ?_ hp))
  intro x _
  simp only [hbot]
  exact Set.notMem_empty x

end Vanishing

end Stacks.EtaleCohomology

end
