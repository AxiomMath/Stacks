module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InjectiveSystemVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemSectionsColimit

/-!
# Étale cohomology of the colimit of a system of sheaves over a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms `f_{i'i}`, let `(F_i, φ_{i'i})` be a system of abelian
sheaves on the small étale sites of the `X_i` ([Stacks, Tag 0EZL]), `f_i : X ⟶ X_i` the
projections and `𝓕 = colim f_i⁻¹F_i`. Then the pull back maps on étale cohomology induce

`colim_i H^p(X_i, F_i) = H^p(X, 𝓕)` for all `p ≥ 0` ([Stacks, Tag 09YQ]).

## Main definitions

* `Stacks.EtaleCohomology.IsEtaleCohomologyColimit`: the assertion that the pull back maps
  exhibit `H^p(X, 𝓕)` as the colimit of the `H^p(X_i, F_i)`.

## Main results

* `Stacks.EtaleCohomology.EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback`: the theorem
  ([Stacks, Tag 09YQ]).
* `Stacks.EtaleCohomology.EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback_zero`: the
  case `p = 0`.
* `Stacks.EtaleCohomology.EtaleSheafSystem.isEtaleCohomologyColimit_succ_of_shortExact`: the
  inductive step along a short exact sequence of systems.
* `Stacks.EtaleCohomology.etaleCohomologyPullback_equiv₀`: in degree zero the pull back map is
  the map on global sections given by the unit of the inverse image.

## Implementation notes

The source computes the cohomology of `𝓕` on the site `X_{affine,étale}` and applies the
colimit theorem for cohomology over a colimit of sites. Here the theorem is proved on the small
étale site of `X` itself, by induction on the degree. In degree zero it is the colimit formula
for sections over a quasi-compact separated object
(`Stacks.EtaleCohomology.EtaleSheafSystem.exists_pushforwardLeg_apply_eq`,
`Stacks.EtaleCohomology.EtaleSheafSystem.exists_pushforwardTransition_apply_eq_zero`). In the
inductive step the system is embedded into a system of injective sheaves, whose colimit has
vanishing higher cohomology, and the long exact cohomology sequences present the cohomology in
degree `p + 1` as a cokernel of the cohomology in degree `p`. The system need not satisfy
`φ_{ii} = id`: colimits are colimits of systems (`CategoryTheory.Limits.IsSystemColimit`).

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Identities are étale, so the identity is the final object of a small étale site. -/
local instance : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  ⟨fun _ => inferInstance⟩

/-! ### The pull back map in degree zero -/

section DegreeZero

variable {X Y : Scheme.{u}}

/-- The degree zero cohomology class of a map out of the constant sheaf is its adjoint section
over the final object. -/
lemma smallEtale_equiv₀_mk₀ (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    (x : (constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal _ _) (Ext.mk₀ x) =
      (smallEtaleConstantAdj X).homEquiv _ _ x ⟨1⟩ := by
  have h : Ext.addEquiv₀ (Ext.mk₀ x) = x := (AddEquiv.eq_symm_apply Ext.addEquiv₀).mp rfl
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, h]
  rfl

/-- **The pull back map in degree zero, on global sections.** For `f : X ⟶ Y` and
`φ : f⁻¹F ⟶ G`, the pull back of a global section `s` of `F` is `φ` applied to the restriction of
the image of `s` under the unit of `f⁻¹ ⊣ f_*` to the final object of the small étale site of
`X`. -/
lemma etaleCohomologyPullback_equiv₀ (f : X ⟶ Y) {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}}
    {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : (smallEtalePullbackAb f).obj F ⟶ G)
    (y : Sheaf.H.{u + 1} F 0) :
    Sheaf.H.equiv₀ G (MorphismProperty.Over.mkIdTerminal _ _) (etaleCohomologyPullback f φ 0 y) =
      φ.hom.app _ (((smallEtalePullbackAb f).obj F).obj.map
        ((smallEtaleBaseChangeFinalIsTerminal f).from (Scheme.Etale.mk (𝟙 X))).op
          (smallEtalePullbackAbUnitApp f F _
            (Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal _ _) y))) := by
  obtain ⟨x, rfl⟩ : ∃ x, Ext.mk₀ x = y := ⟨Ext.addEquiv₀ y, Ext.addEquiv₀.symm_apply_apply y⟩
  rw [etaleCohomologyPullback_mk₀, smallEtale_equiv₀_mk₀, smallEtale_equiv₀_mk₀,
    ← Category.assoc, Adjunction.homEquiv_naturality_right, ConcreteCategory.comp_apply]
  refine congrArg (φ.hom.app _) ?_
  have key := leftAdjointCompIso_inv_homEquiv_symm (smallEtaleConstantAdj Y)
    (smallEtaleAdjunctionAb f) (smallEtaleConstantAdj X) (smallEtalePushforwardAbΓIso f)
    ((smallEtaleConstantAdj Y).homEquiv _ _ x) ((smallEtaleAdjunctionAb f).homEquiv _ _ (𝟙 _))
  simp only [Equiv.symm_apply_apply, Category.comp_id] at key
  rw [smallEtalePullbackAbConstantIso, (Equiv.eq_symm_apply _).mp key]
  simp only [ConcreteCategory.comp_apply, smallEtalePushforwardAbΓIso_hom_app]
  rfl

/-- **The pull back map in degree zero, at a final object.** Let `W` be a final object of the
small étale site of `Y` and `w` a section of `F` over `W`. The pull back of the global section
of `F` given by `w` is, at any morphism `g` from the final object of the small étale site of `X`
to the base change of `W`, the image of `w` under the unit of `f⁻¹ ⊣ f_*` followed by `φ`. -/
lemma etaleCohomologyPullback_equiv₀_of_isTerminal (f : X ⟶ Y)
    {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb f).obj F ⟶ G) {W : Y.Etale} (hW : IsTerminal W)
    (w : ToType (F.obj.obj (op W))) (g : Scheme.Etale.mk (𝟙 X) ⟶ (smallEtaleBaseChange f).obj W) :
    Sheaf.H.equiv₀ G (MorphismProperty.Over.mkIdTerminal _ _)
        (etaleCohomologyPullback f φ 0
          ((Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal _ _)).symm
          (F.obj.map (hW.from (Scheme.Etale.mk (𝟙 Y))).op w))) =
      G.obj.map g.op (φ.hom.app _ (smallEtalePullbackAbUnitApp f F W w)) := by
  have hT : IsTerminal ((smallEtaleBaseChange f).obj W) :=
    hW.isTerminalObj (smallEtaleBaseChange f) _
  rw [etaleCohomologyPullback_equiv₀, AddEquiv.apply_symm_apply,
    smallEtalePullbackAbUnitApp_naturality, presheaf_map_map_apply,
    ← hT.hom_ext g (((smallEtaleBaseChangeFinalIsTerminal f).from (Scheme.Etale.mk (𝟙 X))) ≫
    (smallEtaleBaseChange f).map (hW.from (Scheme.Etale.mk (𝟙 Y))))]
  exact congrArg (fun ψ => ψ (smallEtalePullbackAbUnitApp f F W w)) (φ.hom.naturality g.op)

end DegreeZero

/-! ### The system of cohomology groups -/

section System

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}

variable (c : Cone D) in
/-- The assertion of Stacks 09YQ in degree `p` for a system `F` and a family `ι` of maps
`f_i⁻¹F_i ⟶ 𝓕`: the pull back maps exhibit `H^p(X, 𝓕)` as the colimit of the system of the
`H^p(X_i, F_i)`. -/
abbrev IsEtaleCohomologyColimit (p : ℕ) (F : EtaleSheafSystem D Ab.{u + 1})
    (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕) : Prop :=
  IsSystemColimit (fun i => AddCommGrpCat.of (Sheaf.H.{u + 1} (F.obj i) p))
    (fun a => AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map a) (F.map a) p))
    (AddCommGrpCat.of (Sheaf.H.{u + 1} 𝓕 p))
    (fun i => AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app i) (ι i) p))

/-- **The pull back maps of a system of sheaves compose**, by the cocycle condition. -/
lemma EtaleSheafSystem.etaleCohomologyPullback_map_comp (F : EtaleSheafSystem D Ab.{u + 1})
    {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) (p : ℕ) (x : Sheaf.H.{u + 1} (F.obj k) p) :
    etaleCohomologyPullback (D.map (a ≫ b)) (F.map (a ≫ b)) p x =
      etaleCohomologyPullback (D.map a) (F.map a) p
        (etaleCohomologyPullback (D.map b) (F.map b) p x) := by
  rw [etaleCohomologyPullback_comp (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b),
    ← systemPullbackComp_eq, F.map_comp]

/-- **The pull back maps to the limit are compatible with the system.** -/
lemma EtaleSheafSystem.etaleCohomologyPullback_π_comp (F : EtaleSheafSystem D Ab.{u + 1})
    (c : Cone D) {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    {ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓖}
    (hι : LimitHigherDirectImage.IsPullbackCocone c F ι) {i j : Iᵒᵖ} (a : i ⟶ j) (p : ℕ)
    (x : Sheaf.H.{u + 1} (F.obj j) p) :
    etaleCohomologyPullback (c.π.app i) (ι i) p (etaleCohomologyPullback (D.map a) (F.map a) p x) =
      etaleCohomologyPullback (c.π.app j) (ι j) p x := by
  rw [etaleCohomologyPullback_comp (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm,
    ← conePullbackComp_eq, hι a]

end System

/-! ### Degree zero -/

section ColimitDegreeZero

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)
  (F : EtaleSheafSystem D Ab.{u + 1}) {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
  (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓖)

/-- The pull back to the limit of a global section of a stage, through a leg pushed to an
earlier stage. -/
lemma EtaleSheafSystem.equiv₀_etaleCohomologyPullback_π {k i₀ : Iᵒᵖ} (a : k ⟶ i₀)
    (x : ToType ((F.obj k).obj.obj
      (op ((smallEtaleBaseChange (D.map a)).obj (Scheme.Etale.mk (𝟙 (D.obj i₀))))))) :
    Sheaf.H.equiv₀ 𝓖 (MorphismProperty.Over.mkIdTerminal _ _)
        (etaleCohomologyPullback (c.π.app k) (ι k) 0
          ((Sheaf.H.equiv₀ (F.obj k) (MorphismProperty.Over.mkIdTerminal _ _)).symm
            ((F.obj k).obj.map ((smallEtaleBaseChangeFinalIsTerminal (D.map a)).from
              (Scheme.Etale.mk (𝟙 (D.obj k)))).op x))) =
      𝓖.obj.map ((smallEtaleBaseChangeFinalIsTerminal (c.π.app i₀)).from
          (Scheme.Etale.mk (𝟙 c.pt))).op
        ((F.pushforwardLeg c ι a).hom.app (op (Scheme.Etale.mk (𝟙 (D.obj i₀)))) x) := by
  rw [EtaleSheafSystem.pushforwardLeg_app_apply, presheaf_map_map_apply]
  exact etaleCohomologyPullback_equiv₀_of_isTerminal (c.π.app k) (ι k)
    (smallEtaleBaseChangeFinalIsTerminal (D.map a)) x _

/-- The pull back along a transition of a global section of a stage, through the transition
pushed to an earlier stage. -/
lemma EtaleSheafSystem.equiv₀_etaleCohomologyPullback_map {l k i₀ : Iᵒᵖ} (b : l ⟶ k)
    (a : k ⟶ i₀) (x : ToType ((F.obj k).obj.obj
      (op ((smallEtaleBaseChange (D.map a)).obj (Scheme.Etale.mk (𝟙 (D.obj i₀))))))) :
    Sheaf.H.equiv₀ (F.obj l) (MorphismProperty.Over.mkIdTerminal _ _)
        (etaleCohomologyPullback (D.map b) (F.map b) 0
          ((Sheaf.H.equiv₀ (F.obj k) (MorphismProperty.Over.mkIdTerminal _ _)).symm
            ((F.obj k).obj.map ((smallEtaleBaseChangeFinalIsTerminal (D.map a)).from
              (Scheme.Etale.mk (𝟙 (D.obj k)))).op x))) =
      (F.obj l).obj.map ((smallEtaleBaseChangeFinalIsTerminal (D.map (b ≫ a))).from
          (Scheme.Etale.mk (𝟙 (D.obj l)))).op
        ((F.pushforwardTransition b a).hom.app (op (Scheme.Etale.mk (𝟙 (D.obj i₀)))) x) := by
  rw [EtaleSheafSystem.pushforwardTransition_app_apply, presheaf_map_map_apply]
  exact etaleCohomologyPullback_equiv₀_of_isTerminal (D.map b) (F.map b)
    (smallEtaleBaseChangeFinalIsTerminal (D.map a)) x _

end ColimitDegreeZero

section ColimitDegreeZeroTheorem

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c)

/-- The final object of a small étale site of a compact scheme is compact. -/
private instance compactSpace_left_mk_id {X : Scheme.{u}} [CompactSpace X] :
    CompactSpace (Scheme.Etale.mk (𝟙 X)).left := ‹_›

/-- The final object of a small étale site of a qcqs scheme is quasi-separated. -/
private instance quasiSeparatedSpace_left_mk_id {X : Scheme.{u}} [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace (Scheme.Etale.mk (𝟙 X)).left := ‹_›

/-- Restriction between two final objects of a small étale site is inverse to restriction the
other way. -/
lemma map_map_of_isTerminal {X : Scheme.{u}} (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    {T T' : X.Etale} (hT : IsTerminal T) (hT' : IsTerminal T') (g : T ⟶ T') (g' : T' ⟶ T)
    (s : ToType (G.obj.obj (op T))) : G.obj.map g.op (G.obj.map g'.op s) = s := by
  rw [presheaf_map_map_apply, hT.hom_ext (g ≫ g') (𝟙 _), op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]

include hc in
/-- **The degree zero case of Stacks 09YQ.** The pull back maps on global sections exhibit the
global sections of the colimit `𝓖 = colim f_i⁻¹F_i` as the colimit of the system of global
sections of the `F_i`. -/
theorem EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback_zero
    (F : EtaleSheafSystem D Ab.{u + 1}) {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓖)
    (hι : LimitHigherDirectImage.IsPullbackCocone c F ι)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓖 F ι) :
    IsSystemColimit (fun i => AddCommGrpCat.of (Sheaf.H.{u + 1} (F.obj i) 0))
      (fun a => AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map a) (F.map a) 0))
      (AddCommGrpCat.of (Sheaf.H.{u + 1} 𝓖 0))
      (fun i => AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app i) (ι i) 0)) := by
  have hT0 : IsTerminal (Scheme.Etale.mk (𝟙 c.pt)) := MorphismProperty.Over.mkIdTerminal _ _
  refine IsSystemColimit.of_forall_exists.{u, u + 1} (I := I)
    (fun a b => by ext x; exact F.etaleCohomologyPullback_map_comp a b 0 x)
    (fun a => by ext x; exact F.etaleCohomologyPullback_π_comp c hι a 0 x) ?_ ?_
  · intro s
    obtain ⟨i₀⟩ : Nonempty Iᵒᵖ := inferInstance
    let V₀ := Scheme.Etale.mk (𝟙 (D.obj i₀))
    let hVt := smallEtaleBaseChangeFinalIsTerminal (c.π.app i₀)
    obtain ⟨k, a, x, hx⟩ := EtaleSheafSystem.exists_pushforwardLeg_apply_eq c hc F ι hι hpres V₀
      (𝓖.obj.map (hT0.from _).op (Sheaf.H.equiv₀ 𝓖 (MorphismProperty.Over.mkIdTerminal _ _) s))
    refine ⟨k, (Sheaf.H.equiv₀ (F.obj k) (MorphismProperty.Over.mkIdTerminal _ _)).symm
      ((F.obj k).obj.map ((smallEtaleBaseChangeFinalIsTerminal (D.map a)).from
        (Scheme.Etale.mk (𝟙 (D.obj k)))).op x), ?_⟩
    refine (Sheaf.H.equiv₀ 𝓖 (MorphismProperty.Over.mkIdTerminal _ _)).injective
      ((F.equiv₀_etaleCohomologyPullback_π c ι a x).trans ?_)
    rw [hx, map_map_of_isTerminal 𝓖 hT0 hVt]
  · intro i y hy
    let V₀ := Scheme.Etale.mk (𝟙 (D.obj i))
    let hTi : IsTerminal V₀ := MorphismProperty.Over.mkIdTerminal _ _
    let hW := smallEtaleBaseChangeFinalIsTerminal (D.map (𝟙 i))
    let hVt := smallEtaleBaseChangeFinalIsTerminal (c.π.app i)
    let x := (F.obj i).obj.map (hTi.from ((smallEtaleBaseChange (D.map (𝟙 i))).obj V₀)).op
      (Sheaf.H.equiv₀ (F.obj i) (MorphismProperty.Over.mkIdTerminal _ _) y)
    have hyx : y = (Sheaf.H.equiv₀ (F.obj i) (MorphismProperty.Over.mkIdTerminal _ _)).symm
        ((F.obj i).obj.map (hW.from V₀).op x) := by
      rw [map_map_of_isTerminal (F.obj i) hTi hW, AddEquiv.symm_apply_apply]
    have h0 := F.equiv₀_etaleCohomologyPullback_π c ι (𝟙 i) x
    rw [← hyx, show etaleCohomologyPullback (c.π.app i) (ι i) 0 y = 0 from hy, map_zero] at h0
    have hx0 : (F.pushforwardLeg c ι (𝟙 i)).hom.app (op V₀) x = 0 :=
      (map_map_of_isTerminal 𝓖 hVt hT0 (hT0.from _) (hVt.from _) _).symm.trans
        ((congrArg _ h0.symm).trans (map_zero _))
    obtain ⟨l, b, hb⟩ := EtaleSheafSystem.exists_pushforwardTransition_apply_eq_zero c hc F ι hι
      hpres V₀ (𝟙 i) x hx0
    refine ⟨l, b, (Sheaf.H.equiv₀ (F.obj l) (MorphismProperty.Over.mkIdTerminal _ _)).injective ?_⟩
    show Sheaf.H.equiv₀ (F.obj l) _ (etaleCohomologyPullback (D.map b) (F.map b) 0 y) = _
    rw [hyx, F.equiv₀_etaleCohomologyPullback_map b (𝟙 i) x, hb, map_zero]
    exact map_zero _

end ColimitDegreeZeroTheorem

/-! ### The inductive step -/

section Induction

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  {c : Cone D}

/-- In a short exact sequence `0 ⟶ F ⟶ G ⟶ Q ⟶ 0` of abelian sheaves with `G` injective, the
connecting map `H^p(Q) ⟶ H^{p+1}(F)` is surjective. -/
lemma surjective_comp_extClass_of_injective {X : Scheme.{u}}
    {S : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS : S.ShortExact) (p : ℕ)
    (hG : Subsingleton (Sheaf.H.{u + 1} S.X₂ (p + 1))) :
    Function.Surjective (fun x : Sheaf.H.{u + 1} S.X₃ p => x.comp hS.extClass rfl) :=
  fun y => Ext.covariant_sequence_exact₁ _ hS y (Subsingleton.elim _ _) rfl

/-- The composite `H^p(G) ⟶ H^p(Q) ⟶ H^{p+1}(F)` attached to a short exact sequence vanishes. -/
lemma comp_mk₀_g_comp_extClass {X : Scheme.{u}}
    {S : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS : S.ShortExact) {p : ℕ}
    (x : Sheaf.H.{u + 1} S.X₂ p) :
    (x.comp (Ext.mk₀ S.g) (add_zero p)).comp hS.extClass rfl = 0 := by
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- In a short exact sequence `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓠 ⟶ 0` of abelian sheaves with `H^{p+1}(𝓖) = 0`,
the connecting map `H^p(𝓠) ⟶ H^{p+1}(𝓕)` is a cokernel of `H^p(𝓖) ⟶ H^p(𝓠)`. -/
def isColimitCokernelCoforkExtClass {X : Scheme.{u}}
    {S : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS : S.ShortExact) (p : ℕ)
    (hG : Subsingleton (Sheaf.H.{u + 1} S.X₂ (p + 1))) :
    IsColimit (CokernelCofork.ofπ (Z := AddCommGrpCat.of (Sheaf.H.{u + 1} S.X₁ (p + 1)))
      (f := AddCommGrpCat.ofHom ((Ext.mk₀ S.g).postcomp _ (add_zero p)))
      (AddCommGrpCat.ofHom (hS.extClass.postcomp _ rfl))
      (by ext x; exact comp_mk₀_g_comp_extClass hS x)) := by
  let T := ShortComplex.mk (AddCommGrpCat.ofHom ((Ext.mk₀ S.g).postcomp
      ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)))
      (add_zero p)))
    (AddCommGrpCat.ofHom (hS.extClass.postcomp
      ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) rfl))
    (by ext x; exact comp_mk₀_g_comp_extClass hS x)
  have : Epi T.g := (AddCommGrpCat.epi_iff_surjective _).mpr
    (surjective_comp_extClass_of_injective hS p hG)
  exact ((ShortComplex.ab_exact_iff T).mpr fun x hx =>
    Ext.covariant_sequence_exact₃ _ hS x rfl hx).gIsCokernel

/-- Pulling back commutes with composition with maps of sheaves compatible with the pull back
data. -/
lemma etaleCohomologyPullback_comp_mk₀_of_comm {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Sheaf (smallEtaleTopology Y) Ab.{u + 1}}
    {A' B' : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb f).obj A ⟶ A') (ψ : (smallEtalePullbackAb f).obj B ⟶ B')
    (g : A ⟶ B) (g' : A' ⟶ B') (h : (smallEtalePullbackAb f).map g ≫ ψ = φ ≫ g') (p : ℕ)
    (x : Sheaf.H.{u + 1} A p) :
    (etaleCohomologyPullback f φ p x).comp (Ext.mk₀ g') (add_zero p) =
      etaleCohomologyPullback f ψ p (x.comp (Ext.mk₀ g) (add_zero p)) := by
  rw [etaleCohomologyPullback_comp_mk₀, etaleCohomologyPullback_mk₀_comp, h]

/-- **The inductive step of Stacks 09YQ for one short exact sequence.** Let
`0 ⟶ F ⟶ G ⟶ Q ⟶ 0` be a short exact sequence of systems with `G` injective and
`0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓠 ⟶ 0` a compatible short exact sequence of colimit presentations with
`H^{p+1}(𝓖) = 0`. If the assertion holds in degree `p` for `G` and `Q`, it holds in degree
`p + 1` for `F`. -/
theorem EtaleSheafSystem.isEtaleCohomologyColimit_succ_of_shortExact (p : ℕ)
    {F G Q : EtaleSheafSystem D Ab.{u + 1}} (α : ∀ i, F.obj i ⟶ G.obj i)
    (β : ∀ i, G.obj i ⟶ Q.obj i) (hαβ : ∀ i, α i ≫ β i = 0)
    (hE : ∀ i, (ShortComplex.mk (α i) (β i) (hαβ i)).ShortExact)
    (hα : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback D Ab.{u + 1} a).map (α j) ≫ G.map a = F.map a ≫ α i)
    (hβ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (systemPullback D Ab.{u + 1} a).map (β j) ≫ Q.map a = G.map a ≫ β i)
    (hGi : ∀ i, Subsingleton (Sheaf.H.{u + 1} (G.obj i) (p + 1)))
    {𝓕 𝓖 𝓠 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (G.obj i) ⟶ 𝓖)
    (ιQ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (Q.obj i) ⟶ 𝓠)
    (hιG : LimitHigherDirectImage.IsPullbackCocone c G ιG) (u : 𝓕 ⟶ 𝓖) (v : 𝓖 ⟶ 𝓠)
    (huv : u ≫ v = 0) (hlim : (ShortComplex.mk u v huv).ShortExact)
    (hu : ∀ i, (smallEtalePullbackAb (c.π.app i)).map (α i) ≫ ιG i = ι i ≫ u)
    (hv : ∀ i, (smallEtalePullbackAb (c.π.app i)).map (β i) ≫ ιQ i = ιG i ≫ v)
    (hA : IsEtaleCohomologyColimit c p G 𝓖 ιG) (hB : IsEtaleCohomologyColimit c p Q 𝓠 ιQ)
    (hvan : Subsingleton (Sheaf.H.{u + 1} 𝓖 (p + 1))) :
    IsEtaleCohomologyColimit c (p + 1) F 𝓕 ι :=
  IsSystemColimit.of_cokernel
    (fun i => AddCommGrpCat.ofHom ((Ext.mk₀ (β i)).postcomp _ (add_zero p)))
    (fun i => AddCommGrpCat.ofHom ((hE i).extClass.postcomp _ rfl))
    (fun i => AddCommGrpCat.ext fun x => comp_mk₀_g_comp_extClass (hE i) x)
    (fun i => (AddCommGrpCat.epi_iff_surjective _).mpr
      (surjective_comp_extClass_of_injective (hE i) p (hGi i)))
    (fun {i j} a => AddCommGrpCat.ext fun x =>
      etaleCohomologyPullback_comp_extClass (D.map a) (hE j) (hE i) (F.map a) (G.map a)
        (Q.map a) (hα a) (hβ a) p x)
    (fun i => AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app i) (ι i) (p + 1))) hA hB
    (fun a => AddCommGrpCat.ext fun x => G.etaleCohomologyPullback_π_comp c hιG a p x)
    (AddCommGrpCat.ofHom ((Ext.mk₀ v).postcomp _ (add_zero p)))
    (AddCommGrpCat.ofHom (hlim.extClass.postcomp _ rfl))
    (fun i => AddCommGrpCat.ext fun x =>
      etaleCohomologyPullback_comp_mk₀_of_comm (c.π.app i) (ιG i) (ιQ i) (β i) v (hv i) p x)
    (fun i => by
      ext x
      exact etaleCohomologyPullback_comp_extClass (c.π.app i) (hE i) hlim (ι i) (ιG i) (ιQ i)
        (hu i) (hv i) p x)
    (isColimitCokernelCoforkExtClass hlim p hvan)

/-- **The inductive step of Stacks 09YQ.** If the assertion holds in degree `p` for every system
with a colimit presentation, and `H^{p+1}` vanishes on the colimit of every system of injective
sheaves, then the assertion holds in degree `p + 1` for every system with a colimit
presentation: embed the system into a system of injective sheaves and present the cohomology in
degree `p + 1` as the cokernel of the cohomology in degree `p` of the quotient. -/
theorem EtaleSheafSystem.isEtaleCohomologyColimit_succ (p : ℕ)
    (hvan : ∀ (G : EtaleSheafSystem D Ab.{u + 1}) [∀ i, Injective (G.obj i)]
      (𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
      (ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (G.obj i) ⟶ 𝓖),
      LimitHigherDirectImage.IsPullbackCocone c G ιG →
      LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓖 G ιG →
      Subsingleton (Sheaf.H.{u + 1} 𝓖 (p + 1)))
    (ih : ∀ (F : EtaleSheafSystem D Ab.{u + 1}) (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
      (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕),
      LimitHigherDirectImage.IsPullbackCocone c F ι →
      LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι →
      IsEtaleCohomologyColimit c p F 𝓕 ι)
    (F : EtaleSheafSystem D Ab.{u + 1}) (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : LimitHigherDirectImage.IsPullbackCocone c F ι)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι) :
    IsEtaleCohomologyColimit c (p + 1) F 𝓕 ι := by
  obtain ⟨G, _, Q, α, β, hαβ, 𝓖, 𝓠, ιG, ιQ, u, v, huv, hE, hα, hβ, hιG, hG, hιQ, hQ, hlim, hu,
    hv⟩ := LimitHigherDirectImage.exists_injective_shortExact_presentation c F 𝓕 ι hι hpres
  exact isEtaleCohomologyColimit_succ_of_shortExact p α β hαβ hE hα hβ
    (fun i => ⟨fun x y => (Ext.eq_zero_of_injective x).trans (Ext.eq_zero_of_injective y).symm⟩)
    ι ιG ιQ hιG u v huv hlim hu hv (ih G 𝓖 ιG hιG hG) (ih Q 𝓠 ιQ hιQ hQ) (hvan G 𝓖 ιG hιG hG)

end Induction

section AllDegrees

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c)

include hc in
/-- **Stacks 09YQ, given the vanishing of the higher cohomology of the colimit of a system of
injective sheaves.** The induction on the degree, starting from
`Stacks.EtaleCohomology.EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback_zero`. -/
theorem EtaleSheafSystem.isEtaleCohomologyColimit_of_vanishing
    (hvan : ∀ (q : ℕ) (G : EtaleSheafSystem D Ab.{u + 1}) [∀ i, Injective (G.obj i)]
      (𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
      (ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (G.obj i) ⟶ 𝓖),
      LimitHigherDirectImage.IsPullbackCocone c G ιG →
      LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓖 G ιG →
      Subsingleton (Sheaf.H.{u + 1} 𝓖 (q + 1)))
    (p : ℕ) (F : EtaleSheafSystem D Ab.{u + 1}) (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : LimitHigherDirectImage.IsPullbackCocone c F ι)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι) :
    IsEtaleCohomologyColimit c p F 𝓕 ι := by
  induction p generalizing F 𝓕 ι with
  | zero => exact F.isSystemColimit_etaleCohomologyPullback_zero hc ι hι hpres
  | succ p ih => exact EtaleSheafSystem.isEtaleCohomologyColimit_succ p (hvan p) ih F 𝓕 ι hι hpres

include hc in
/-- **Étale cohomology commutes with limits of quasi-compact quasi-separated schemes with affine
transition morphisms** ([Stacks, Tag 09YQ]). Let `X = lim X_i` be the limit of a directed
inverse system of quasi-compact and quasi-separated schemes with affine transition morphisms,
`(F_i, φ_{i'i})` a system of abelian sheaves on the small étale sites of the `X_i`, and
`ι_i : f_i⁻¹F_i ⟶ 𝓕` a colimit of the system of the inverse images on the small étale site of
`X`. Then for every `p` the pull back maps `H^p(X_i, F_i) ⟶ H^p(X, 𝓕)` exhibit `H^p(X, 𝓕)` as
the colimit of the system of the `H^p(X_i, F_i)`. -/
@[stacks 09YQ]
theorem EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback (p : ℕ)
    (F : EtaleSheafSystem D Ab.{u + 1}) (𝓕 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hι : LimitHigherDirectImage.IsPullbackCocone c F ι)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι) :
    IsSystemColimit (fun i => AddCommGrpCat.of (Sheaf.H.{u + 1} (F.obj i) p))
      (fun a => AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map a) (F.map a) p))
      (AddCommGrpCat.of (Sheaf.H.{u + 1} 𝓕 p))
      (fun i => AddCommGrpCat.ofHom (etaleCohomologyPullback (c.π.app i) (ι i) p)) :=
  EtaleSheafSystem.isEtaleCohomologyColimit_of_vanishing hc
    (fun q G _ _ ιG hιG hG => EtaleSheafSystem.subsingleton_H_of_injective hc G ιG hιG hG q)
    p F 𝓕 ι hι hpres

end AllDegrees

end Stacks.EtaleCohomology

end
