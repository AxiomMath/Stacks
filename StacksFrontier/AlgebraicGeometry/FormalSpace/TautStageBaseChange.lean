module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.Topology.Algebra.AdicTopology.Completion
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut

/-!
# Base change of a morphism of formal spectra along a thickening stage

Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over a
scheme `S`, and let `I` be a weak ideal of definition of `A`. If the closure `K` of `φ(I)C` is
again a weak ideal of definition of `C` — which is exactly what tautness of `φ` asserts — then
the square
```
Spec (C ⧸ K) ⟶ Spec (A ⧸ I)
     ↓               ↓
   Spf C     ⟶     Spf A
```
is cartesian. This is the computation `C ⧸ K = C ⊗̂_A A ⧸ I` of Stacks 0AN5, read as a fibre
product of fppf sheaves rather than as an identity of rings.

## Main results

* `AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage`: the displayed square is
  cartesian whenever the closure of the extended ideal is a weak ideal of definition.
* `AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_stage_of_isTaut`: the same for a
  taut homomorphism, where the hypothesis on the closure is automatic.
* `AlgebraicGeometry.FormalSpace.isWeakIdealOfDefinition_closure_map_of_isPullback`: the
  converse reading of the same square, and the heart of the implication (1) ⟹ (3) of
  Stacks 0AN5. If the base change of `Spf φ` along the stage inclusion `Spec (A ⧸ I) ⟶ Spf A`
  is represented by an object of the site, then the closure of `φ(I)C` is a weak ideal of
  definition of `C`.
* `AlgebraicGeometry.FormalSpace.exists_isWeakIdealOfDefinition_map_le`: for every weak ideal
  of definition `L` of `C` there is a weak ideal of definition `I` of `A` with `φ(I)C ⊆ L`.
  This needs no hypothesis on `Spf φ` at all.

The last two are the two halves of that implication, which is assembled in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut`. They live here
because their proofs rest on the file-private stage lemmas comparing the ideals cut out by two
stage inclusions, which is also what the cartesian square above is built from.

## Implementation notes

The cartesian square is produced by exhibiting the formal spectrum of the source as a filtered
colimit of its own stages and factoring the projection of the fibre product through the stage
`Spec (C ⧸ K)` one colimit index at a time. Three ingredients make the stagewise factorisation
available. The stage inclusion `Spec (C ⧸ K) ⟶ Spf C` is a monomorphism, because the
transition morphisms of the presenting diagram are closed immersions and the sections of a
filtered colimit of sheaves are the colimit of the sections. It is a representable thickening,
by Stacks 0AIC through
`AlgebraicGeometry.FormalSpace.QuotientSystem.weakIdealColimitPresentation`. And a
representable thickening into `Spf C` is classified by a weak ideal of definition of `C`, again
by Stacks 0AIC; comparing that ideal with `K` on the nose is the only place where the rings
themselves are touched, and it is done by reading the induced homomorphism of quotients off the
commuting square through the full faithfulness of `Spec`.

Passing from the stagewise factorisations to a single factorisation uses that filtered colimits
of sheaves of types are exact, so that the fibre product of the colimit cocone with a fixed
morphism is again a colimit cocone.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AMS](https://stacks.math.columbia.edu/tag/0AMS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe w₂ w₁ v u

section Bridges

/-- A morphism into a filtered colimit factors through a monomorphism as soon as each of its
base changes to a colimit stage does, provided colimits of that shape are exact. -/
private theorem factor_through_mono_of_colimit_pullbacks
    {D : Type*} [Category D] {I : Type*} [Category I] [IsConnected I]
    [HasPullbacks D] [HasColimitsOfShape I D] [HasExactColimitsOfShape I D]
    {G : I ⥤ D} {c : Cocone G} (hc : IsColimit c)
    {X K : D} (p : X ⟶ c.pt) (m : K ⟶ c.pt) [Mono m]
    (h : ∀ i, ∃ l : pullback (c.ι.app i) p ⟶ K,
      l ≫ m = pullback.snd (c.ι.app i) p ≫ p) :
    ∃ l : X ⟶ K, l ≫ m = p := by
  classical
  choose l hl using h
  let H := pullback c.ι ((Functor.const I).map p)
  let t := pullback.snd c.ι ((Functor.const I).map p)
  have hli (i) : ((pullbackObjIso c.ι ((Functor.const I).map p) i).hom ≫ l i) ≫ m =
      t.app i ≫ p := by
    rw [Category.assoc, hl, ← Category.assoc]
    exact congrArg (fun q => q ≫ p)
      (pullbackObjIso_hom_comp_snd c.ι ((Functor.const I).map p) i)
  let d : Cocone H := {
    pt := K
    ι := {
      app i := (pullbackObjIso c.ι ((Functor.const I).map p) i).hom ≫ l i
      naturality i j f := by
        apply (cancel_mono m).1
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          Category.assoc]
        rw [← Category.assoc _ (l j) m, hli, ← Category.assoc, t.naturality]
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        simpa only [Category.assoc] using (hli i).symm } }
  let hd := hc.pullbackOfHasExactColimitsOfShape p
  refine ⟨hd.desc d, hd.hom_ext (fun i => ?_)⟩
  rw [← Category.assoc, hd.fac d i]
  exact hli i

/-- Rewriting a commuting square along an isomorphism of its upper-left corner. -/
theorem comp_eq_of_map_iso_of_map_hom
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U V T : C} {X Y : D} (e : U ≅ V) (i : F.obj V ⟶ X)
    (p : F.obj U ⟶ X) (f : X ⟶ Y) (q : U ⟶ T) (ξ : F.obj T ⟶ Y)
    (hp : F.map e.hom ≫ i = p) (hw : p ≫ f = F.map q ≫ ξ) :
    i ≫ f = F.map (e.inv ≫ q) ≫ ξ := by
  apply (cancel_epi (F.map e.hom)).1
  rw [F.map_comp, ← Category.assoc, hp]
  simpa only [← Category.assoc, ← F.map_comp, e.hom_inv_id, F.map_id,
    Category.id_comp] using hw

/-- Rewriting a commuting square along an isomorphism of its upper-left corner.

The file-private form of `comp_eq_of_map_iso_of_map_hom`. -/
private alias comp_eq_of_map_iso := comp_eq_of_map_iso_of_map_hom

end Bridges

section WeakIdealIndex

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- The weak ideals of definition of a weakly pre-admissible ring are nonempty. -/
private theorem weakIdeals_nonempty' (hR : TopologicalRing.IsWeaklyPreAdmissible R) :
    Nonempty (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :=
  ⟨⟨hR.choose, hR.choose_spec⟩⟩

/-- The weak ideals of definition of a topological ring are directed under reverse
inclusion. -/
private theorem weakIdeals_directed' :
    IsDirected (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) :=
  ⟨fun I J => ⟨⟨I.1 ⊓ J.1, I.2.1.inter J.2.1, fun x hx => I.2.2 x hx.1⟩,
    show I.1 ⊓ J.1 ≤ I.1 from inf_le_left,
    show I.1 ⊓ J.1 ≤ J.1 from inf_le_right⟩⟩

end WeakIdealIndex

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section StageInclusion

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- A stage inclusion of a formal spectrum is a monomorphism. -/
private theorem formalSpectrumInclusion_mono
    (hR : TopologicalRing.IsWeaklyPreAdmissible R)
    (D : QuotientSystem B S hS R)
    (I : OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    Mono (formalSpectrumInclusion D I) := by
  let : Nonempty (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :=
    weakIdeals_nonempty' hR
  let : IsDirected (OrderDual { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) := weakIdeals_directed'
  apply Sheaf.mono_colimit_ι_of_mono_transition
  intro J K g
  apply Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying
    (BigFppfOver.topology B S hS) (BigFppfOver.toScheme B S hS)
  change Mono (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom g))))
  let : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom g)))) :=
    IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective (leOfHom g))
  infer_instance

/-- A transition morphism of the presenting diagram composed with a stage inclusion is the
stage inclusion of the smaller ideal. -/
private theorem formalSpectrumInclusion_comp_transition
    (D : QuotientSystem B S hS R)
    (I J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) (h : I.1 ≤ J.1) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D.transition h)) ≫
      formalSpectrumInclusion D I = formalSpectrumInclusion D J :=
  colimit.w (formalSpectrumDiagram D) (homOfLE h)

/-- A stage inclusion of a formal spectrum is a representable thickening. -/
theorem formalSpectrumInclusion_isThickening_stage
    [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (D : QuotientSystem B S hS R)
    (I : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (formalSpectrumInclusion D I) := by
  let J : WeakIdeals R := OrderDual.toDual I
  convert isThickening_quotient B S hS R (formalSpectrum D)
    D.weakIdealColimitPresentation hR J using 1 <;> rfl

/-- A stage inclusion of a formal spectrum is a representable thickening.

The file-private form of `formalSpectrumInclusion_isThickening_stage`. -/
private alias formalSpectrumInclusion_isThickening := formalSpectrumInclusion_isThickening_stage

end StageInclusion

section IdealComparison

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- A relation between a morphism of spectra and the maps induced by two ring homomorphisms is
read off as a relation between the ring homomorphisms. -/
private theorem preimage_spec_comp_eq {X Y Z : Type u} [CommRing X] [CommRing Y] [CommRing Z]
    (g : Spec (.of X) ⟶ Spec (.of Y)) (u : Z →+* Y) (v : Z →+* X)
    (h : g ≫ Spec.map (CommRingCat.ofHom u) = Spec.map (CommRingCat.ofHom v)) :
    (Spec.fullyFaithful.preimage g).unop.hom.comp u = v := by
  change g ≫ Scheme.Spec.map (CommRingCat.ofHom u).op =
    Scheme.Spec.map (CommRingCat.ofHom v).op at h
  rw [← Spec.fullyFaithful.map_preimage g, ← Scheme.Spec.map_comp] at h
  exact congrArg (fun f => f.unop.hom) (Scheme.Spec.map_injective h)

/-- A factorisation of one stage inclusion through another forces an inclusion of the
corresponding weak ideals. -/
theorem ideal_le_of_stage_factorization_weakIdeal
    (hR : TopologicalRing.IsWeaklyPreAdmissible R)
    (D : QuotientSystem B S hS R)
    (I J : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I })
    (g : (BigAffineFppf.inclusion B S hS).obj (D.stage I) ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.stage J))
    (hg : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
      formalSpectrumInclusion D J = formalSpectrumInclusion D I) :
    J.1 ≤ I.1 := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  let Q := BigFppfOver.toScheme B S hS
  let L : { I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨I.1 ⊓ J.1, I.2.1.inter J.2.1, fun x hx => I.2.2 x hx.1⟩
  let a := T.map (D.transition (show L.1 ≤ I.1 from inf_le_left))
  let b := T.map (D.transition (show L.1 ≤ J.1 from inf_le_right))
  have : Mono (formalSpectrumInclusion D L) :=
    formalSpectrumInclusion_mono B S hS hR D L
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have hab : g ≫ b = a := by
    apply F.map_injective
    apply (cancel_mono (formalSpectrumInclusion D L)).1
    rw [F.map_comp, Category.assoc]
    change F.map g ≫ (F.map b ≫ _) = F.map a ≫ _
    rw [formalSpectrumInclusion_comp_transition B S hS D L J,
      formalSpectrumInclusion_comp_transition B S hS D L I]
    exact hg
  let coord : Spec (.of (R ⧸ I.1)) ⟶ Spec (.of (R ⧸ J.1)) := Q.map g
  let ψ := (Spec.fullyFaithful.preimage coord).unop.hom
  have heq : ψ.comp (Ideal.Quotient.factor (show L.1 ≤ J.1 from inf_le_right)) =
      Ideal.Quotient.factor (show L.1 ≤ I.1 from inf_le_left) :=
    preimage_spec_comp_eq coord _ _ ((Q.map_comp _ _).symm.trans (congrArg Q.map hab))
  intro x hx
  have he := congrArg (fun f : R ⧸ L.1 →+* R ⧸ I.1 => f (Ideal.Quotient.mk L.1 x)) heq
  change ψ (Ideal.Quotient.mk J.1 x) = Ideal.Quotient.mk I.1 x at he
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] at he
  exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm

/-- A factorisation of one stage inclusion through another forces an inclusion of the
corresponding weak ideals.

The file-private form of `ideal_le_of_stage_factorization_weakIdeal`. -/
private alias ideal_le_of_stage_factorization := ideal_le_of_stage_factorization_weakIdeal

end IdealComparison

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]

/-- A commuting square from a stage of the source spectrum to a stage of the target spectrum
forces the extended ideal to be contained in the source stage's ideal. -/
theorem map_ideal_le_of_formalSpectrum_square_weakIdeal
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (J : { J : Ideal C // TopologicalRing.IsWeakIdealOfDefinition J })
    (g : (BigAffineFppf.inclusion B S hS).obj (E.stage J) ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (hg : formalSpectrumInclusion E J ≫ formalSpectrumMap hA f =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map g ≫
        formalSpectrumInclusion D I) :
    I.1.map f.toRingHom ≤ J.1 := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  let Q := BigFppfOver.toScheme B S hS
  let L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨I.1 ⊓ Ideal.comap f.toRingHom J.1,
      I.2.1.inter (J.2.1.preimage f.continuous), fun x hx => I.2.2 x hx.1⟩
  let a := T.map (f.stageMap L J (show L.1 ≤ Ideal.comap f.toRingHom J.1 from inf_le_right))
  let b := T.map (D.transition (show L.1 ≤ I.1 from inf_le_left))
  have : Mono (formalSpectrumInclusion D L) :=
    formalSpectrumInclusion_mono B S hS hA.1 D L
  have : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  have hab : g ≫ b = a := by
    apply F.map_injective
    apply (cancel_mono (formalSpectrumInclusion D L)).1
    rw [F.map_comp, Category.assoc]
    change F.map g ≫ (F.map b ≫ _) = F.map a ≫ _
    rw [formalSpectrumInclusion_comp_transition B S hS D L I]
    exact hg.symm.trans (formalSpectrumMap_spec hA f L J inf_le_right)
  let coord : Spec (.of (C ⧸ J.1)) ⟶ Spec (.of (A ⧸ I.1)) := Q.map g
  let ψ := (Spec.fullyFaithful.preimage coord).unop.hom
  have heq : ψ.comp (Ideal.Quotient.factor (show L.1 ≤ I.1 from inf_le_left)) =
      Ideal.quotientMap J.1 f.toRingHom
        (show L.1 ≤ Ideal.comap f.toRingHom J.1 from inf_le_right) :=
    preimage_spec_comp_eq coord _ _ ((Q.map_comp _ _).symm.trans (congrArg Q.map hab))
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  have he := congrArg (fun f : A ⧸ L.1 →+* C ⧸ J.1 => f (Ideal.Quotient.mk L.1 x)) heq
  change ψ (Ideal.Quotient.mk I.1 x) = Ideal.Quotient.mk J.1 (f.toRingHom x) at he
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero] at he
  change f.toRingHom x ∈ J.1
  exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm

/-- A commuting square from a stage of the source spectrum to a stage of the target spectrum
forces the extended ideal to be contained in the source stage's ideal.

The file-private form of `map_ideal_le_of_formalSpectrum_square_weakIdeal`. -/
private alias map_ideal_le_of_formalSpectrum_square :=
  map_ideal_le_of_formalSpectrum_square_weakIdeal

variable [IsTopologicalRing C] [IsLinearTopology C C]

/-- A representable thickening into the target spectrum which fits in a commuting square over a
stage of the source spectrum factors through the stage cut out by the closure of the extended
ideal. -/
private theorem factor_through_closure_stage
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K })
    (hK : K.1 = (I.1.map f.toRingHom).closure)
    (U : BigFppfOver B S hS)
    (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ formalSpectrum E)
    (q : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (hp : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) p)
    (hw : p ≫ formalSpectrumMap hA f =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q ≫
        formalSpectrumInclusion D I) :
    ∃ l : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶
        (formalSpectrumDiagram E).obj K,
      l ≫ formalSpectrumInclusion E K = p := by
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let T := BigAffineFppf.inclusion B S hS
  obtain ⟨J, e, he⟩ := (existsUnique_weakIdeal_quotient B S hS C (formalSpectrum E)
    E.weakIdealColimitPresentation hC U p hp.rep hp).exists
  change F.map e.hom ≫ formalSpectrumInclusion E J = p at he
  have hs := comp_eq_of_map_iso F e _ p _ q _ he hw
  have hIJ := map_ideal_le_of_formalSpectrum_square B S hS hA D E f I J (e.inv ≫ q) hs
  have hKJ : K.1 ≤ J.1 := by
    rw [hK]
    exact closure_minimal hIJ (J.1.toAddSubgroup.isClosed_of_isOpen J.2.1)
  refine ⟨F.map (e.hom ≫ T.map (E.transition hKJ)), ?_⟩
  rw [F.map_comp, Category.assoc]
  exact (congrArg (fun z => F.map e.hom ≫ z)
    (formalSpectrumInclusion_comp_transition B S hS E K J hKJ)).trans he

/-- **The stage base change of Stacks 0AN5.** Let `φ : A ⟶ C` be a continuous homomorphism of
weakly admissible topological rings over `S`, let `I` be a weak ideal of definition of `A`, and
suppose the closure `K` of `φ(I)C` is a weak ideal of definition of `C`. Then the square of
fppf sheaves formed by the two stage inclusions and `Spf φ` is cartesian: `Spec (C ⧸ K)` is the
fibre product `Spf C ×_{Spf A} Spec (A ⧸ I)`. -/
theorem isPullback_formalSpectrumMap_stage
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K })
    (hK : K.1 = (I.1.map f.toRingHom).closure)
    (hIK : I.1 ≤ Ideal.comap f.toRingHom K.1) :
    IsPullback (formalSpectrumInclusion E K)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (f.stageMap I K hIK)))
      (formalSpectrumMap hA f) (formalSpectrumInclusion D I) := by
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let T := BigAffineFppf.inclusion B S hS
  let Q := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let G := formalSpectrumDiagram E
  let φ : colimit (formalSpectrumDiagram E) ⟶ colimit (formalSpectrumDiagram D) :=
    formalSpectrumMap hA f
  let i : (formalSpectrumDiagram D).obj I ⟶ colimit (formalSpectrumDiagram D) :=
    formalSpectrumInclusion D I
  let k : (formalSpectrumDiagram E).obj K ⟶ colimit (formalSpectrumDiagram E) :=
    formalSpectrumInclusion E K
  let a := F.map (T.map (f.stageMap I K hIK))
  let P := pullback i φ
  let p : P ⟶ colimit (formalSpectrumDiagram E) := pullback.snd i φ
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : MorphismProperty.IsStableUnderComposition
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) :=
    isThickening_isStableUnderComposition
  let : Q.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let : Nonempty (OrderDual { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }) :=
    weakIdeals_nonempty' hC.1
  let : IsDirected (OrderDual { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
      (· ≤ ·) := weakIdeals_directed'
  let : Mono k := formalSpectrumInclusion_mono B S hS hC.1 E (OrderDual.toDual K)
  let : Mono i := formalSpectrumInclusion_mono B S hS hA.1 D (OrderDual.toDual I)
  have hi : Q.relative F i := formalSpectrumInclusion_isThickening B S hS hA D I
  have hstage (L : WeakIdeals C) :
      ∃ l : pullback (colimit.ι G L) p ⟶ F.obj (T.obj (E.stage K)),
        l ≫ k = pullback.snd (colimit.ι G L) p ≫ p := by
    let iL : (formalSpectrumDiagram E).obj L ⟶ colimit (formalSpectrumDiagram E) :=
      formalSpectrumInclusion E L
    let ξ := iL ≫ φ
    let U := hi.rep.pullback ξ
    let r := hi.rep.fst ξ
    let q := hi.rep.snd ξ
    let s := F.map q ≫ iL
    have hs : Q.relative F s := (Q.relative F).comp_mem _ _
      ((Q.relative_isStableUnderBaseChange).of_isPullback (hi.rep.isPullback ξ) hi)
      (formalSpectrumInclusion_isThickening B S hS hC E L)
    have hsi : s ≫ φ = r ≫ i :=
      (Category.assoc (F.map q) iL φ).trans (hi.rep.w ξ).symm
    let r' := F.preimage r
    have hr' : F.map r' = r := F.map_preimage r
    obtain ⟨l, hl⟩ := factor_through_closure_stage B S hS hA hC D E f I K hK U s r' hs
      (by rw [hr']; exact hsi)
    let b := pullback.snd (colimit.ι G L) p
    let c := pullback.fst (colimit.ι G L) p
    have hcond1 : pullback.fst i φ ≫ i = p ≫ φ := pullback.condition
    have hcond2 : c ≫ iL = b ≫ p := pullback.condition
    have hw : (b ≫ pullback.fst i φ) ≫ i = c ≫ ξ := by
      rw [Category.assoc, hcond1, ← Category.assoc, ← hcond2]
      exact Category.assoc _ _ _
    let d := (hi.rep.isPullback ξ).lift (b ≫ pullback.fst i φ) c hw
    have hd : d ≫ F.map q = c := (hi.rep.isPullback ξ).lift_snd _ _ hw
    refine ⟨d ≫ l, ?_⟩
    rw [Category.assoc, hl, ← hcond2, ← hd]
    exact (Category.assoc _ _ _).symm
  let : IsFiltered (OrderDual { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }) :=
    inferInstance
  let : IsConnected (OrderDual { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I }) :=
    IsFiltered.isConnected _
  let : HasExactColimitsOfShape
      (OrderDual { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
      (Sheaf J (Type (u + 1))) := by
    let : AB5OfSize.{u, u} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1, u + 1, u + 2} (C := Type (u + 1))
    infer_instance
  obtain ⟨l, hl⟩ := factor_through_mono_of_colimit_pullbacks (colimit.isColimit G) p k hstage
  have hw : k ≫ φ = a ≫ i := formalSpectrumMap_spec hA f I K hIK
  refine ⟨⟨hw⟩, ⟨?_⟩⟩
  have hfst (c : PullbackCone φ i) :
      (pullback.lift c.snd c.fst c.condition.symm ≫ l) ≫ k = c.fst :=
    calc (pullback.lift c.snd c.fst c.condition.symm ≫ l) ≫ k
        = pullback.lift c.snd c.fst c.condition.symm ≫ l ≫ k := Category.assoc _ _ _
      _ = pullback.lift c.snd c.fst c.condition.symm ≫ p :=
        congrArg (fun z => pullback.lift c.snd c.fst c.condition.symm ≫ z) hl
      _ = c.fst := pullback.lift_snd _ _ _
  refine PullbackCone.IsLimit.mk hw
    (fun c => pullback.lift c.snd c.fst c.condition.symm ≫ l) hfst ?_ ?_
  · intro c
    apply (cancel_mono i).1
    have hfst := hfst c
    calc ((pullback.lift c.snd c.fst c.condition.symm ≫ l) ≫ a) ≫ i
        = (pullback.lift c.snd c.fst c.condition.symm ≫ l) ≫ a ≫ i := Category.assoc _ _ _
      _ = (pullback.lift c.snd c.fst c.condition.symm ≫ l) ≫ k ≫ φ :=
        congrArg (fun z => (pullback.lift c.snd c.fst c.condition.symm ≫ l) ≫ z) hw.symm
      _ = ((pullback.lift c.snd c.fst c.condition.symm ≫ l) ≫ k) ≫ φ :=
        (Category.assoc _ _ _).symm
      _ = c.fst ≫ φ := congrArg (fun z => z ≫ φ) hfst
      _ = c.snd ≫ i := c.condition
  · intro c m hm hn
    apply (cancel_mono k).1
    rw [hm]
    calc c.fst = pullback.lift c.snd c.fst c.condition.symm ≫ p :=
        (pullback.lift_snd _ _ _).symm
      _ = pullback.lift c.snd c.fst c.condition.symm ≫ l ≫ k :=
        congrArg (fun z => pullback.lift c.snd c.fst c.condition.symm ≫ z) hl.symm
      _ = (pullback.lift c.snd c.fst c.condition.symm ≫ l) ≫ k :=
        (Category.assoc _ _ _).symm

/-- **The stage base change of Stacks 0AN5 for a taut homomorphism.** For a taut continuous
homomorphism `φ : A ⟶ C` of weakly admissible topological rings over `S` and a weak ideal of
definition `I` of `A`, the closure of `φ(I)C` is a weak ideal of definition of `C` and the
square formed by the two stage inclusions and `Spf φ` is cartesian. -/
theorem isPullback_formalSpectrumMap_stage_of_isTaut
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    ∃ (K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K })
      (_hK : K.1 = (I.1.map f.toRingHom).closure)
      (hIK : I.1 ≤ Ideal.comap f.toRingHom K.1),
      IsPullback (formalSpectrumInclusion E K)
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (f.stageMap I K hIK)))
        (formalSpectrumMap hA f) (formalSpectrumInclusion D I) := by
  let K : { K : Ideal C // TopologicalRing.IsWeakIdealOfDefinition K } :=
    ⟨(I.1.map f.toRingHom).closure, hf.1 I.1 I.2.1,
      TopologicalRing.closure_map_le_topologicalNilradical f.toRingHom f.continuous I.1 I.2.2⟩
  have hIK : I.1 ≤ Ideal.comap f.toRingHom K.1 :=
    Ideal.map_le_iff_le_comap.mp subset_closure
  exact ⟨K, rfl, hIK, isPullback_formalSpectrumMap_stage B S hS hA hC D E f I K rfl hIK⟩

omit [IsTopologicalRing A] in
/-- The sum of the extension of a weak ideal of definition of the source with a weak ideal of
definition of the target is a weak ideal of definition of the target: it is open because it
contains an open ideal, and its elements are topologically nilpotent because both summands
lie in the topological nilradical. -/
private theorem isWeakIdealOfDefinition_sup_map (φ : A →+* C) (hφ : Continuous φ)
    {I : Ideal A} (hI : TopologicalRing.IsWeakIdealOfDefinition I)
    {L : Ideal C} (hL : TopologicalRing.IsWeakIdealOfDefinition L) :
    TopologicalRing.IsWeakIdealOfDefinition (I.map φ ⊔ L) := by
  refine ⟨TopologicalRing.isOpen_sup_of_isOpen_right hL.1, fun x hx => ?_⟩
  have hsub : I.map φ ≤ Ideal.closure (I.map φ) := subset_closure
  have hcl : Ideal.closure (I.map φ) ≤ topologicalNilradical C :=
    TopologicalRing.closure_map_le_topologicalNilradical φ hφ I
      (fun y hy => IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hI.2 y hy))
  have hnil : I.map φ ⊔ L ≤ topologicalNilradical C :=
    sup_le (hsub.trans hcl)
      (fun y hy => IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr (hL.2 y hy))
  exact IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mp (hnil hx)

/-- Rewriting a factorisation through an isomorphism of the middle object. -/
private theorem map_comp_comp_eq_of_map_iso
    {C₁ C₂ : Type*} [Category C₁] [Category C₂] (F : C₁ ⥤ C₂)
    {T U V : C₁} {X : C₂} (e : U ≅ V) (i : F.obj V ⟶ X) (p : F.obj U ⟶ X) (m : T ⟶ U)
    (s : F.obj T ⟶ X) (hp : F.map e.hom ≫ i = p) (hm : F.map m ≫ p = s) :
    F.map (m ≫ e.hom) ≫ i = s := by
  rw [F.map_comp, Category.assoc, hp, hm]

/-- **The openness of the extended ideal.** Let `φ : A ⟶ C` be a continuous homomorphism of
weakly admissible topological rings over `S` and let `I` be a weak ideal of definition of `A`.
Suppose the base change of `Spf φ` along the stage inclusion `Spec (A ⧸ I) ⟶ Spf A` is
represented by an object `W` of the site. Then the closure of `φ(I)C` is a weak ideal of
definition of `C`; in particular it is open.

This is the content of the implication (1) ⟹ (3) of Stacks 0AN5: representability of `Spf φ`
is used only to produce `W`. -/
theorem isWeakIdealOfDefinition_closure_map_of_isPullback
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (W : BigFppfOver B S hS)
    (q : W ⟶ (BigAffineFppf.inclusion B S hS).obj (D.stage I))
    (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj W ⟶ formalSpectrum E)
    (hpb : IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
      (formalSpectrumMap hA f) (formalSpectrumInclusion D I)) :
    TopologicalRing.IsWeakIdealOfDefinition
      (Ideal.closure ((I : Ideal A).map f.toRingHom)) := by
  classical
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let Q := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hsub : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  let _ : F.Full := Sheaf.sheafifiedYoneda_full (BigFppfOver.topology B S hS)
  -- the stage inclusion is a representable thickening, by Stacks 0AIC
  have hxi : Q.relative F (formalSpectrumInclusion D I) :=
    formalSpectrumInclusion_isThickening B S hS hA D I
  have hp : Q.relative F p :=
    (MorphismProperty.relative_isStableUnderBaseChange Q).of_isPullback hpb.flip hxi
  obtain ⟨J, e, he⟩ := (existsUnique_weakIdeal_quotient B S hS C (formalSpectrum E)
    E.weakIdealColimitPresentation hC W p hp.1 hp).exists
  change F.map e.hom ≫ formalSpectrumInclusion E J = p at he
  have hsq := comp_eq_of_map_iso F e (formalSpectrumInclusion E J) p
    (formalSpectrumMap hA f) q (formalSpectrumInclusion D I) he hpb.w
  have hIJ : (I : Ideal A).map f.toRingHom ≤ J.1 :=
    map_ideal_le_of_formalSpectrum_square B S hS hA D E f I J (e.inv ≫ q) hsq
  have hle : ∀ L : { L : Ideal C // TopologicalRing.IsWeakIdealOfDefinition L },
      (I : Ideal A).map f.toRingHom ≤ (L : Ideal C) → J.1 ≤ (L : Ideal C) := by
    intro L hIL
    have hcomap : (I : Ideal A) ≤ Ideal.comap f.toRingHom (L : Ideal C) :=
      Ideal.map_le_iff_le_comap.mp hIL
    have hw : formalSpectrumInclusion E L ≫ formalSpectrumMap hA f =
        F.map ((BigAffineFppf.inclusion B S hS).map (f.stageMap I L hcomap)) ≫
          formalSpectrumInclusion D I := formalSpectrumMap_spec hA f I L hcomap
    have hmp := hpb.lift_fst (formalSpectrumInclusion E L)
      (F.map ((BigAffineFppf.inclusion B S hS).map (f.stageMap I L hcomap))) hw
    obtain ⟨m, hm⟩ := F.map_surjective (hpb.lift (formalSpectrumInclusion E L)
      (F.map ((BigAffineFppf.inclusion B S hS).map (f.stageMap I L hcomap))) hw)
    refine ideal_le_of_stage_factorization B S hS hC.1 E L J (m ≫ e.hom) ?_
    exact map_comp_comp_eq_of_map_iso F e (formalSpectrumInclusion E J) p m
      (formalSpectrumInclusion E L) he ((congrArg (fun z => z ≫ p) hm).trans hmp)
  have hJ : Ideal.closure ((I : Ideal A).map f.toRingHom) = J.1 := by
    refine le_antisymm (closure_minimal hIJ
      (J.1.toAddSubgroup.isClosed_of_isOpen J.2.1)) ?_
    intro x hx
    refine (TopologicalRing.mem_closure_iff_forall_sup_isOpen
      ((I : Ideal A).map f.toRingHom) x).mpr ?_
    intro K hK
    obtain ⟨L₀, hL₀, hL₀K⟩ :=
      (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hC).mem_iff.mp
        (hK.mem_nhds K.zero_mem)
    have hwid := isWeakIdealOfDefinition_sup_map f.toRingHom f.continuous I.2 hL₀
    have hmem := hle ⟨_, hwid⟩ le_sup_left hx
    exact sup_le_sup_left (show L₀ ≤ K from fun y hy => hL₀K hy) _ hmem
  rw [hJ]
  exact J.2

omit [IsTopologicalRing C] [IsLinearTopology C C] in
/-- **Cofinality of the extended ideals.** For every weak ideal of definition `L` of `C` there
is a weak ideal of definition `I` of `A` with `φ(I)C ⊆ L`.

No hypothesis on `Spf φ` is needed: the stage `Spec (C ⧸ L)` is an affine scheme, so the
morphism `Spec (C ⧸ L) ⟶ Spf A` it induces factors through a stage `Spec (A ⧸ I)` of `Spf A` by
Stacks 0AIA, and the commuting square so produced forces the inclusion of ideals. -/
theorem exists_isWeakIdealOfDefinition_map_le
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (L : { L : Ideal C // TopologicalRing.IsWeakIdealOfDefinition L }) :
    ∃ I : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      (I : Ideal A).map f.toRingHom ≤ (L : Ideal C) := by
  classical
  let F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let _ : Nonempty (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :=
    weakIdeals_nonempty' hA.1
  let _ : IsDirected
      (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) (· ≤ ·) :=
    weakIdeals_directed'
  obtain ⟨j, g, hg⟩ := exists_factor_to_affine_stage B S hS (formalSpectrum D)
    (OrderDual { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    D.diagram (fun _ _ h => D.isThickening_map_diagram h) (Iso.refl _) (E.stage L)
    (formalSpectrumInclusion E L ≫ formalSpectrumMap hA f)
  refine ⟨j, map_ideal_le_of_formalSpectrum_square B S hS hA D E f j L
    ((BigAffineFppf.inclusion B S hS).map g) ?_⟩
  exact hg.symm

end AlgebraicGeometry.FormalSpace

end
