module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedInSetoids.Setoid
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses

/-!
# Schlessinger's condition (S2) for the associated functor

Condition (S2) for the functor of isomorphism classes associated
to a category cofibered in groupoids satisfying the Rim-Schlessinger condition.

## Main results

* `schlessingerConditionS2_of_isIsomorphismClasses`
  transfers (S2) to the canonical associated functor.

## Implementation notes

The associated functor is the canonical functor of fibrewise isomorphism
classes constructed in `isomorphismClasses`. Its action on base
morphisms is part of that construction. Since the source is cofibered in
groupoids, being a setoid on the special fibre also covers the case where that
fibre is a set. The automorphism-lifting condition says that every vertical
automorphism of the image of a dual-number object lifts to a vertical
automorphism commuting with its projection.

## References

* [Stacks Project, Tag 06I0](https://stacks.math.columbia.edu/tag/06I0)
-/

@[expose] public section

namespace Deformation

/-! ### Schlessinger's condition (S2) for the associated functor -/

section
open CategoryTheory
universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Private bridges -/

/-- Equivalence with a one-object category makes every fibre morphism an
isomorphism and kills its endomorphisms. -/
private theorem setoid_of_equiv_punit {C : Type u₂} [Category.{v₂} C]
    (E : C ≌ Discrete PUnit.{u₂ + 1}) : IsSetoidCategory C := by
  have : E.functor.Full := E.full_functor
  have : E.functor.Faithful := E.faithful_functor
  have : E.functor.ReflectsIsomorphisms :=
    Functor.FullyFaithful.reflectsIsomorphisms (E.fullyFaithfulFunctor)
  constructor
  · intro X Y f
    exact Functor.ReflectsIsomorphisms.reflects E.functor f
  · intro X f
    exact E.functor.map_injective (Subsingleton.elim _ _)

/-- An object of a skeletal target fibre is represented by an object of the
source fibre, and the representative can be chosen with its image equal to
the given object. -/
private theorem fiber_rep_exact
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    (φ : BasedFunctor 𝓕 𝓖)
    (hφ : IsIsomorphismClasses φ)
    (y : 𝓖.obj) (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k) (hy : 𝓖.p.obj y = A) :
    ∃ x : Functor.Fiber 𝓕.p A, φ.obj x.1 = y := by
  have : (fiberFunctor φ A).EssSurj := hφ.fiber_essSurj A
  obtain ⟨x, ⟨i⟩⟩ :=
    Functor.EssSurj.mem_essImage (fiberFunctor φ A) ⟨y, hy⟩
  exact ⟨x, congrArg Subtype.val (hφ.fiber_skeletal A ⟨i⟩)⟩

/-- The map of an arrow under a based functor agrees with its original base
map after the canonical endpoint transports. -/
private theorem basedFunctor_map_eq_transport
    {C : Type u} [Category.{v} C]
    {𝓕 : BasedCategory.{v₁, u₁} C} {𝓖 : BasedCategory.{v₂, u₂} C}
    (φ : BasedFunctor 𝓕 𝓖) {a b : 𝓕.obj} (f : a ⟶ b) :
    𝓖.p.map (φ.toFunctor.map f) =
      eqToHom (φ.w_obj a) ≫ 𝓕.p.map f ≫ eqToHom (φ.w_obj b).symm := by
  have : 𝓖.p.IsHomLift (𝓕.p.map f) (φ.toFunctor.map f) :=
    BasedFunctor.preserves_isHomLift φ (𝓕.p.map f) f
  simpa using IsHomLift.fac' 𝓖.p (𝓕.p.map f) (φ.toFunctor.map f)

/-- Fullness lifts an arrow between images of objects, together with its base map. -/
private theorem exists_preimage_with_base
    {C : Type u} [Category.{v} C]
    {𝓕 : BasedCategory.{v₁, u₁} C} {𝓖 : BasedCategory.{v₂, u₂} C}
    (φ : BasedFunctor 𝓕 𝓖) (hfull : φ.toFunctor.Full)
    {a b : 𝓕.obj} {y z : 𝓖.obj} (hy : φ.obj a = y) (hz : φ.obj b = z)
    (ha : 𝓕.p.obj a = 𝓖.p.obj y) (hb : 𝓕.p.obj b = 𝓖.p.obj z) (f : y ⟶ z) :
    ∃ f' : a ⟶ b, φ.toFunctor.map f' = eqToHom hy ≫ f ≫ eqToHom hz.symm ∧
      𝓕.p.map f' = eqToHom ha ≫ 𝓖.p.map f ≫ eqToHom hb.symm := by
  subst hy hz
  obtain ⟨f', rfl⟩ := hfull.map_surjective f
  refine ⟨f', by simp, ?_⟩
  simp [basedFunctor_map_eq_transport φ f']

/-- Two arrows over the same base map with the same image differ by a vertical
automorphism of their common codomain. -/
private theorem cofibered_verticalAut_adjust
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    {p : F ⥤ C} (hp : p.op.IsFiberedInGroupoids)
    {x y : F} (f g : x ⟶ y)
    (hbase : p.map f = p.map g) :
    ∃ a : y ≅ y, p.map a.hom = 𝟙 (p.obj y) ∧ f ≫ a.hom = g := by
  have hcomm : (𝟙 (Opposite.op (p.obj y))) ≫ p.op.map f.op = p.op.map g.op := by
    simpa using congrArg Quiver.Hom.op hbase
  obtain ⟨aop, ⟨haMap, haComp⟩, _⟩ :=
    hp.unique_lift f.op g.op (𝟙 (Opposite.op (p.obj y))) hcomm
  let a : y ⟶ y := aop.unop
  have hLiftOp : p.op.IsHomLift (𝟙 (Opposite.op (p.obj y))) aop := by
    apply IsHomLift.of_fac' p.op _ aop rfl rfl
    simpa using haMap
  have : p.op.IsStronglyCartesian (𝟙 (Opposite.op (p.obj y))) aop :=
    hp.isStronglyCartesian_homLift (𝟙 (Opposite.op (p.obj y))) aop
  have : IsIso aop :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso
      (p := p.op) (f := 𝟙 (Opposite.op (p.obj y))) aop
  have : IsIso a := CategoryTheory.isIso_of_op a
  exact ⟨asIso a, by simpa [a, Functor.op_map] using congrArg Quiver.Hom.unop haMap,
    by simpa [a, Functor.op_map] using congrArg Quiver.Hom.unop haComp⟩

/-- The residue morphism is an isomorphism when the source algebra is
isomorphic to the residue field as a Λ-algebra. -/
private noncomputable def algEquivToResidueFieldIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (i : A ≃ₐ[Λ] k) :
    A ≅ residueFieldObject Λ k := by
  classical
  let : IsField A := MulEquiv.isField (Field.toIsField k) i.toMulEquiv
  have hmax : IsLocalRing.maximalIdeal (↑A) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp ‹IsField A›
  let resAlg : A →ₐ[Λ] IsLocalRing.ResidueField A :=
    IsScalarTower.toAlgHom Λ A (IsLocalRing.ResidueField A)
  let q : A →ₐ[Λ] ULift.{v} k :=
    (ULift.algEquiv (R := Λ) (A := k)).symm.toAlgHom.comp
      (A.residueEquiv.toAlgHom.comp resAlg)
  have hq : Function.Bijective q := by
    refine ⟨fun a b hab => ?_, (ULift.algEquiv (R := Λ) (A := k)).symm.surjective.comp
      (A.residueEquiv.surjective.comp (IsLocalRing.residue_surjective (R := A)))⟩
    have hres : IsLocalRing.residue A a = IsLocalRing.residue A b :=
      A.residueEquiv.injective ((ULift.algEquiv (R := Λ) (A := k)).symm.injective hab)
    have hm := (IsLocalRing.residue_eq_zero_iff (a - b)).mp (by rw [map_sub, hres, sub_self])
    rw [hmax] at hm
    exact sub_eq_zero.mp hm
  let qe : A ≃ₐ[Λ] ULift.{v} k := AlgEquiv.ofBijective q hq
  let K := residueFieldObject Λ k
  let f : A ⟶ K := {
    hom := q
    isLocal := ⟨fun _ h => (MulEquiv.isUnit_map qe.toMulEquiv).mp h⟩
    residue_comm := by
      intro a
      have hK : IsLocalRing.maximalIdeal (↑K) = ⊥ := by
        change IsLocalRing.maximalIdeal (ULift.{v} k) = ⊥
        exact IsLocalRing.maximalIdeal_eq_bot
      change
        ((Ideal.quotientEquivAlgOfEq Λ hK).trans
            ((AlgEquiv.quotientBot Λ (ULift.{v} k)).trans
              (ULift.algEquiv (R := Λ) (A := k))))
          (IsLocalRing.residue K (q a)) = A.residueEquiv (IsLocalRing.residue A a)
      rw [IsLocalRing.residue_def]
      simp only [AlgEquiv.trans_apply]
      rw [Ideal.quotientEquivAlgOfEq_mk, AlgEquiv.quotientBot_mk]
      simp [q, resAlg, AlgHom.comp_apply, IsLocalRing.ResidueField.algebraMap_eq]
  }
  let g : K ⟶ A := {
    hom := qe.symm.toAlgHom
    isLocal := ⟨fun _ h => (MulEquiv.isUnit_map qe.symm.toMulEquiv).mp h⟩
    residue_comm := by
      intro z
      obtain ⟨a, rfl⟩ := hq.2 z
      simpa [f, qe] using (f.residue_comm a).symm
  }
  exact ⟨f, g, ArtinianLocalAlgCat.hom_ext (AlgHom.ext qe.symm_apply_apply),
    ArtinianLocalAlgCat.hom_ext (AlgHom.ext qe.apply_symm_apply)⟩

/-- A setoid special fibre forces a vertical automorphism to be trivial after
transport along an isomorphism of base objects. -/
private theorem aut_eq_id_of_iso_base_fiberSetoid
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    {p : F ⥤ C} (hp : p.op.IsFiberedInGroupoids)
    {x : F} {K : C} (u : p.obj x ≅ K)
    (hK : IsSetoidCategory (Functor.Fiber p K))
    (a : x ≅ x) (ha : p.map a.hom = 𝟙 (p.obj x)) : a.hom = 𝟙 x := by
  obtain ⟨zop, φop, hφ⟩ := hp.exists_lift u.hom.op (Opposite.op x) rfl
  let z : F := zop.unop
  let f : x ⟶ z := φop.unop
  have hz : p.obj z = K := congrArg Opposite.unop (IsHomLift.domain_eq (p := p.op) u.hom.op φop)
  have hmap : p.map f = u.hom ≫ eqToHom hz.symm := by
    have hh := IsHomLift.fac' (p := p.op) u.hom.op φop
    simpa [z, f, Functor.op_map, Category.assoc] using
      congrArg Quiver.Hom.unop hh
  have : p.op.IsHomLift u.hom.op φop := hφ
  have : p.op.IsStronglyCartesian u.hom.op φop :=
    hp.isStronglyCartesian_homLift u.hom.op φop
  have : IsIso φop :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p.op) (f := u.hom.op) φop
  have : IsIso f := CategoryTheory.isIso_of_op f
  let fi : x ≅ z := asIso f
  let u' : p.obj x ≅ p.obj z := (asIso u.hom) ≪≫ eqToIso hz.symm
  have : p.IsHomLift u'.hom f := by
    apply IsHomLift.of_fac' p u'.hom f rfl rfl
    simpa [u'] using hmap
  have : p.IsHomLift u'.hom fi.hom := by
    simpa [fi] using (inferInstance : p.IsHomLift u'.hom f)
  have : p.IsHomLift u'.inv fi.inv := IsHomLift.inv_lift_inv p u' fi
  let b : z ⟶ z := fi.inv ≫ a.hom ≫ fi.hom
  have hb : p.map b = 𝟙 (p.obj z) := by
    dsimp [b]
    rw [Functor.map_comp, Functor.map_comp, IsHomLift.fac' p u'.hom fi.hom, ha,
      IsHomLift.fac' p u'.inv fi.inv]
    simp [u', Category.assoc]
  have hbLift : p.IsHomLift (𝟙 K) b := by
    apply IsHomLift.of_fac' p (𝟙 K) b hz hz
    simp [hb]
  let zF : Functor.Fiber p K := ⟨z, hz⟩
  let bF : zF ⟶ zF := ⟨b, hbLift⟩
  have hbF : bF = 𝟙 zF := hK.2 zF bF
  have hb' : b = 𝟙 z :=
    congrArg (Functor.Fiber.fiberInclusion (p := p) (S := K)).map hbF
  calc
    a.hom = fi.hom ≫ b ≫ fi.inv := by simp [b]
    _ = 𝟙 x := by simp [hb']

/-- Under either special-fibre rigidity hypothesis, vertical automorphisms
over the residue-field object lift trivially along a dual-number projection.
The final disjunct is already the required lifting condition. -/
private theorem liftVerticalAutomorphism_of_specialFiber
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (h𝓕 : IsCofiberedInGroupoids p)
    (hSpecial :
      (IsPredeformationCategory p) ∨
      (IsSetoidCategory (p.Fiber (residueFieldObject Λ k))) ∨
      (∀ {xε x₀ : F} (e : xε ⟶ x₀),
        IsDualNumberProjection (p.map e) →
        ∀ a : x₀ ≅ x₀, p.map a.hom = 𝟙 (p.obj x₀) →
          ∃ b : xε ≅ xε,
            (p.map b.hom = 𝟙 (p.obj xε)) ∧
              (b.hom ≫ e = e ≫ a.hom)))
    {xε x₀ : F} (e : xε ⟶ x₀)
    (he : IsDualNumberProjection (p.map e))
    (u : p.obj x₀ ≅ residueFieldObject Λ k)
    (a : x₀ ≅ x₀) (ha : p.map a.hom = 𝟙 (p.obj x₀)) :
    ∃ b : xε ≅ xε, (p.map b.hom = 𝟙 (p.obj xε)) ∧
      (b.hom ≫ e = e ≫ a.hom) := by
  rcases hSpecial with hpre | hsetoid | hlift
  · obtain ⟨E⟩ := hpre.specialFiber
    exact ⟨Iso.refl xε, by simp,
      by simp [aut_eq_id_of_iso_base_fiberSetoid h𝓕 u (setoid_of_equiv_punit E) a ha]⟩
  · exact ⟨Iso.refl xε, by simp, by simp [aut_eq_id_of_iso_base_fiberSetoid h𝓕 u hsetoid a ha]⟩
  · exact hlift e he a ha

/-- A base square under a functor of isomorphism classes, over a dual-number
projection, comes from a pullback square over a dual-number projection in the
source. -/
private theorem exists_source_square_of_isIsomorphismClasses
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {φ : BasedFunctor 𝓕 𝓖} (hφ : IsIsomorphismClasses φ)
    {x xε x₀ : 𝓖.obj} (d : x ⟶ x₀) (e : xε ⟶ x₀)
    (hdual : IsDualNumberProjection (𝓖.p.map e))
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (g : Aε ⟶ 𝓖.p.obj x) (gε : Aε ⟶ 𝓖.p.obj xε)
    (hpb : IsPullback gε g (𝓖.p.map e) (𝓖.p.map d)) :
    ∃ (xF : Functor.Fiber 𝓕.p (𝓖.p.obj x))
      (xεF : Functor.Fiber 𝓕.p (𝓖.p.obj xε))
      (x₀F : Functor.Fiber 𝓕.p (𝓖.p.obj x₀))
      (hx : φ.obj xF.1 = x) (hε : φ.obj xεF.1 = xε) (h₀ : φ.obj x₀F.1 = x₀)
      (D : xF.1 ⟶ x₀F.1) (E : xεF.1 ⟶ x₀F.1),
      φ.toFunctor.map D = eqToHom hx ≫ d ≫ eqToHom h₀.symm ∧
      φ.toFunctor.map E = eqToHom hε ≫ e ≫ eqToHom h₀.symm ∧
      IsDualNumberProjection (𝓕.p.map E) ∧
      IsPullback (gε ≫ eqToHom xεF.2.symm) (g ≫ eqToHom xF.2.symm)
        (𝓕.p.map E) (𝓕.p.map D) := by
  obtain ⟨xF, hx⟩ := fiber_rep_exact φ hφ x _ rfl
  obtain ⟨xεF, hε⟩ := fiber_rep_exact φ hφ xε _ rfl
  obtain ⟨x₀F, h₀⟩ := fiber_rep_exact φ hφ x₀ _ rfl
  obtain ⟨D, hD, hDbase⟩ := exists_preimage_with_base φ hφ.full hx h₀ xF.2 x₀F.2 d
  obtain ⟨E, hE, hEbase⟩ := exists_preimage_with_base φ hφ.full hε h₀ xεF.2 x₀F.2 e
  refine ⟨xF, xεF, x₀F, hx, hε, h₀, D, E, hD, hE, ?_, ?_⟩
  · rw [hEbase]
    exact isDualNumberProjection_eqToHom xεF.2 x₀F.2.symm (𝓖.p.map e) hdual
  · apply hpb.of_iso (Iso.refl Aε) (eqToIso xεF.2.symm)
      (eqToIso xF.2.symm) (eqToIso x₀F.2.symm)
      <;> simp [hEbase, hDbase]

/-- A functor of isomorphism classes of a source satisfying (S2) has
completions over dual-number projections. -/
private theorem completion_of_isIsomorphismClasses
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {φ : BasedFunctor 𝓕 𝓖} (hφ : IsIsomorphismClasses φ)
    (hS2 : SchlessingerConditionS2 𝓕.p)
    {x xε x₀ : 𝓖.obj} (d : x ⟶ x₀) (e : xε ⟶ x₀)
    (hdual : IsDualNumberProjection (𝓖.p.map e))
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (g : Aε ⟶ 𝓖.p.obj x) (gε : Aε ⟶ 𝓖.p.obj xε)
    (hpb : IsPullback gε g (𝓖.p.map e) (𝓖.p.map d)) :
    Nonempty (PullbackCompletion 𝓖.p d e g gε) := by
  obtain ⟨xF, xεF, x₀F, hx, hε, h₀, D, E, hD, hE, hdual', hpb'⟩ :=
    exists_source_square_of_isIsomorphismClasses hφ d e hdual g gε hpb
  let g₁ : Aε ⟶ 𝓕.p.obj xF.1 := g ≫ eqToHom xF.2.symm
  let gε₁ : Aε ⟶ 𝓕.p.obj xεF.1 := gε ≫ eqToHom xεF.2.symm
  obtain ⟨P⟩ := hS2.completion D E hdual' g₁ gε₁ hpb'
  refine ⟨{
    apex := φ.obj P.apex
    apex_eq := (φ.w_obj P.apex).trans P.apex_eq
    toFirst := φ.toFunctor.map P.toFirst ≫ eqToHom hx
    toSecond := φ.toFunctor.map P.toSecond ≫ eqToHom hε
    comm := by
      have hc : φ.toFunctor.map P.toSecond ≫ eqToHom hε ≫ e ≫ eqToHom h₀.symm =
          φ.toFunctor.map P.toFirst ≫ eqToHom hx ≫ d ≫ eqToHom h₀.symm := by
        rw [← hE, ← hD]
        simpa only [Functor.map_comp] using congrArg φ.toFunctor.map P.comm
      simpa [Category.assoc] using congrArg (fun t => t ≫ eqToHom h₀) hc
    map_toFirst := ?_
    map_toSecond := ?_ }⟩
  · rw [Functor.map_comp, basedFunctor_map_eq_transport φ P.toFirst, P.map_toFirst]
    simp [g₁, eqToHom_map, Category.assoc]
  · rw [Functor.map_comp, basedFunctor_map_eq_transport φ P.toSecond, P.map_toSecond]
    simp [gε₁, eqToHom_map, Category.assoc]

/-- A completion in the functor of isomorphism classes is the image of a
completion of the corresponding square in the source, once the special fibre
is rigid enough for vertical automorphisms to lift. -/
private theorem exists_sourceCompletion_of_isIsomorphismClasses
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {φ : BasedFunctor 𝓕 𝓖} (hφ : IsIsomorphismClasses φ)
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (hSpecial :
      (IsPredeformationCategory 𝓕.p) ∨
      (IsSetoidCategory (𝓕.p.Fiber (residueFieldObject Λ k))) ∨
      (∀ {xε x₀ : 𝓕.obj} (e : xε ⟶ x₀),
        IsDualNumberProjection (𝓕.p.map e) →
        ∀ a : x₀ ≅ x₀, 𝓕.p.map a.hom = 𝟙 (𝓕.p.obj x₀) →
          ∃ b : xε ≅ xε,
            (𝓕.p.map b.hom = 𝟙 (𝓕.p.obj xε)) ∧
              (b.hom ≫ e = e ≫ a.hom)))
    {x xε x₀ : 𝓖.obj} {d : x ⟶ x₀} {e : xε ⟶ x₀}
    (hdual : IsDualNumberProjection (𝓖.p.map e))
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {g : Aε ⟶ 𝓖.p.obj x} {gε : Aε ⟶ 𝓖.p.obj xε}
    {xF : Functor.Fiber 𝓕.p (𝓖.p.obj x)} {xεF : Functor.Fiber 𝓕.p (𝓖.p.obj xε)}
    {x₀F : Functor.Fiber 𝓕.p (𝓖.p.obj x₀)}
    (hx : φ.obj xF.1 = x) (hε : φ.obj xεF.1 = xε)
    {D : xF.1 ⟶ x₀F.1} {E : xεF.1 ⟶ x₀F.1}
    (hdual' : IsDualNumberProjection (𝓕.p.map E))
    (hpb' : IsPullback (gε ≫ eqToHom xεF.2.symm) (g ≫ eqToHom xF.2.symm)
      (𝓕.p.map E) (𝓕.p.map D))
    (R : PullbackCompletion 𝓖.p d e g gε) :
    ∃ S : PullbackCompletion 𝓕.p D E (g ≫ eqToHom xF.2.symm) (gε ≫ eqToHom xεF.2.symm),
      φ.obj S.apex = R.apex := by
  obtain ⟨i₀, -⟩ := hdual
  let u : 𝓕.p.obj x₀F.1 ≅ residueFieldObject Λ k :=
    eqToIso x₀F.2 ≪≫ algEquivToResidueFieldIso (𝓖.p.obj x₀) i₀
  obtain ⟨RF, hREq⟩ := fiber_rep_exact φ hφ R.apex Aε R.apex_eq
  have lift : ∀ {y : 𝓖.obj} (yF : Functor.Fiber 𝓕.p (𝓖.p.obj y)) (hy : φ.obj yF.1 = y)
      (t : R.apex ⟶ y) (s : Aε ⟶ 𝓖.p.obj y) (ht : 𝓖.p.map t = eqToHom R.apex_eq ≫ s),
      ∃ f : RF.1 ⟶ yF.1, 𝓕.p.map f = eqToHom RF.2 ≫ s ≫ eqToHom yF.2.symm := by
    intro y yF hy t s ht
    obtain ⟨f, -, hf⟩ :=
      exists_preimage_with_base φ hφ.full hREq hy (RF.2.trans R.apex_eq.symm) yF.2 t
    exact ⟨f, by simpa [ht] using hf⟩
  let g₁ : Aε ⟶ 𝓕.p.obj xF.1 := g ≫ eqToHom xF.2.symm
  let gε₁ : Aε ⟶ 𝓕.p.obj xεF.1 := gε ≫ eqToHom xεF.2.symm
  obtain ⟨RFirst, hRFirstBase'⟩ : ∃ f : RF.1 ⟶ xF.1, 𝓕.p.map f = eqToHom RF.2 ≫ g₁ :=
    lift xF hx R.toFirst g R.map_toFirst
  obtain ⟨RSecond, hRSecondBase'⟩ : ∃ f : RF.1 ⟶ xεF.1, 𝓕.p.map f = eqToHom RF.2 ≫ gε₁ :=
    lift xεF hε R.toSecond gε R.map_toSecond
  have hRBaseComp : 𝓕.p.map (RSecond ≫ E) = 𝓕.p.map (RFirst ≫ D) := by
    calc
      𝓕.p.map (RSecond ≫ E) = eqToHom RF.2 ≫ (gε₁ ≫ 𝓕.p.map E) := by
        simp [Functor.map_comp, hRSecondBase', Category.assoc]
      _ = eqToHom RF.2 ≫ (g₁ ≫ 𝓕.p.map D) := by rw [hpb'.w]
      _ = 𝓕.p.map (RFirst ≫ D) := by simp [Functor.map_comp, hRFirstBase', Category.assoc]
  obtain ⟨aR, haRbase, haRcomp⟩ :=
    cofibered_verticalAut_adjust h𝓕 (RSecond ≫ E) (RFirst ≫ D) hRBaseComp
  obtain ⟨bR, hbRbase, hbRcomp⟩ :=
    liftVerticalAutomorphism_of_specialFiber 𝓕.p h𝓕 hSpecial E hdual' u aR haRbase
  refine ⟨{
    apex := RF.1
    apex_eq := RF.2
    toFirst := RFirst
    toSecond := RSecond ≫ bR.hom
    comm := by rw [Category.assoc, hbRcomp, ← Category.assoc, haRcomp]
    map_toFirst := hRFirstBase'
    map_toSecond := by
      rw [Functor.map_comp, hRSecondBase', hbRbase]
      simp [gε₁] }, hREq⟩

/-- Two completions in a functor of isomorphism classes are compared by a
fibre morphism, given (S2) and a rigid special fibre in the source. -/
private theorem comparison_of_isIsomorphismClasses
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, max v w, w} Λ k)}
    [𝓖.p.Faithful] {φ : BasedFunctor 𝓕 𝓖} (hφ : IsIsomorphismClasses φ)
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (hS2 : SchlessingerConditionS2 𝓕.p)
    (hSpecial :
      (IsPredeformationCategory 𝓕.p) ∨
      (IsSetoidCategory (𝓕.p.Fiber (residueFieldObject Λ k))) ∨
      (∀ {xε x₀ : 𝓕.obj} (e : xε ⟶ x₀),
        IsDualNumberProjection (𝓕.p.map e) →
        ∀ a : x₀ ≅ x₀, 𝓕.p.map a.hom = 𝟙 (𝓕.p.obj x₀) →
          ∃ b : xε ≅ xε,
            (𝓕.p.map b.hom = 𝟙 (𝓕.p.obj xε)) ∧
              (b.hom ≫ e = e ≫ a.hom)))
    {x xε x₀ : 𝓖.obj} (d : x ⟶ x₀) (e : xε ⟶ x₀)
    (hdual : IsDualNumberProjection (𝓖.p.map e))
    {Aε : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (g : Aε ⟶ 𝓖.p.obj x) (gε : Aε ⟶ 𝓖.p.obj xε)
    (hpb : IsPullback gε g (𝓖.p.map e) (𝓖.p.map d))
    (P Q : PullbackCompletion 𝓖.p d e g gε) :
    ∃ b : P.apex ⟶ Q.apex, (P.toFirst = b ≫ Q.toFirst) ∧
      (𝓖.p.map b = eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm) := by
  obtain ⟨xF, xεF, x₀F, hx, hε, -, D, E, -, -, hdual', hpb'⟩ :=
    exists_source_square_of_isIsomorphismClasses hφ d e hdual g gε hpb
  obtain ⟨S, hpEq⟩ :=
    exists_sourceCompletion_of_isIsomorphismClasses hφ h𝓕 hSpecial hdual hx hε hdual' hpb' P
  obtain ⟨T, hqEq⟩ :=
    exists_sourceCompletion_of_isIsomorphismClasses hφ h𝓕 hSpecial hdual hx hε hdual' hpb' Q
  obtain ⟨c, -, hcBase⟩ := hS2.comparison D E hdual' _ _ hpb' S T
  let bbase : 𝓖.p.obj P.apex ⟶ 𝓖.p.obj Q.apex := eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm
  let b : P.apex ⟶ Q.apex := eqToHom hpEq.symm ≫ φ.toFunctor.map c ≫ eqToHom hqEq
  have hb : 𝓖.p.map b = bbase := by
    dsimp only [b]
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map,
      basedFunctor_map_eq_transport φ c, eqToHom_map, hcBase]
    simp [bbase]
  refine ⟨b, 𝓖.p.map_injective ?_, hb⟩
  rw [Functor.map_comp, hb, P.map_toFirst, Q.map_toFirst]
  simp [bbase]

/-- The associated functor of isomorphism classes of a category cofibered in
groupoids inherits (S2) if the special fibre is a setoid or automorphisms
over the residue field lift along dual-number projections. In particular this
holds for a predeformation category. -/
@[stacks 06I0 "s2_associated_functor"]
public theorem schlessingerConditionS2_of_isIsomorphismClasses
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k))
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (hS2 : SchlessingerConditionS2 𝓕.p)
    (hSpecial :
      (IsPredeformationCategory 𝓕.p) ∨
      (IsSetoidCategory (𝓕.p.Fiber (residueFieldObject Λ k))) ∨
      (∀ {xε x₀ : 𝓕.obj} (e : xε ⟶ x₀),
        IsDualNumberProjection (𝓕.p.map e) →
        ∀ a : x₀ ≅ x₀, 𝓕.p.map a.hom = 𝟙 (𝓕.p.obj x₀) →
          ∃ b : xε ≅ xε,
            (𝓕.p.map b.hom = 𝟙 (𝓕.p.obj xε)) ∧
              (b.hom ≫ e = e ≫ a.hom))) :
    SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕)) := by
  classical
  let data := isomorphismClassesData 𝓕 h𝓕
  have : (BasedCategory.ofFunctor (Functor.Elements.π data.classes)).p.Faithful :=
    inferInstanceAs (Functor.Elements.π data.classes).Faithful
  change SchlessingerConditionS2 (BasedCategory.ofFunctor (Functor.Elements.π data.classes)).p
  exact ⟨completion_of_isIsomorphismClasses data.quotient hS2,
    comparison_of_isIsomorphismClasses data.quotient h𝓕 hS2 hSpecial⟩

end

end Deformation
