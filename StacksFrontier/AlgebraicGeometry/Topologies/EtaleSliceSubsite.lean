module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSiteBaseChange
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedRefinable
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The small étale subsite of a slice of a site of affine schemes

Let `C` be a category with a functor `L : C ⥤ Sch` and a topology `J` all of whose covering
sieves contain a finite covering family carried by `L` to an étale covering of schemes (`J` is
*étale cofinal* for `L`). For an object `x` of `C`, the objects `V ⟶ x` of the slice `C/x` whose
image under `L` is étale form a full subcategory `C_{x, ét}` of `C/x`, the small étale site of
`x` inside the big site `C/x`. This file equips it with the topology it inherits from `C/x`
and records the facts which make the inclusion `ι : C_{x, ét} ⥤ C/x` a morphism of sites and the
topology of `C_{x, ét}` flatly cofinal for its underlying scheme functor
(`Stacks.AffineSiteBaseChange.IsFlatCofinal`).

## Main definitions

* `Stacks.EtaleSlice.IsEtaleCofinal`: étale cofinality of a topology.
* `Stacks.EtaleSlice.etaleOver`: the objects of `C/x` lying over an étale morphism.
* `Stacks.EtaleSlice.EtaleSlice`: the full subcategory `C_{x, ét}` of `C/x` on those objects.
* `Stacks.EtaleSlice.topology`: the topology `C_{x, ét}` inherits from `C/x`.
* `Stacks.EtaleSlice.toScheme`: the functor `C_{x, ét} ⥤ Sch`.
* `Stacks.EtaleSlice.terminal`: the terminal object `id_x` of `C_{x, ét}`.

## Main results

* `Stacks.EtaleSlice.isContinuous_ι` and `Stacks.EtaleSlice.isCocontinuous_ι`: the inclusion
  `ι` is continuous and cocontinuous.
* `Stacks.EtaleSlice.hasPullbacks`, `Stacks.EtaleSlice.preservesPullbacks_ι` and
  `Stacks.EtaleSlice.isTerminal`: `C_{x, ét}` has fibre products and the terminal object `id_x`,
  and `ι` preserves both, so that `ι` defines a morphism of sites by Stacks 00X6.
* `Stacks.EtaleSlice.isFlatCofinal`: the topology of `C_{x, ét}` is flatly cofinal for
  `toScheme`.
* `Stacks.EtaleSlice.etale_toScheme_map`: every morphism of `C_{x, ét}` lies over an étale
  morphism of schemes.

## References

* [Stacks Project, Tag 00X6](https://stacks.math.columbia.edu/tag/00X6)
* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace Stacks.EtaleSlice

/-- Étale morphisms of schemes, as a `MorphismProperty`. -/
abbrev etaleMorphisms : MorphismProperty Scheme.{u} :=
  @AlgebraicGeometry.Etale

variable {C : Type v} [Category.{w} C] (L : C ⥤ Scheme.{u})

/-- A topology is *étale cofinal* for `L` when every covering sieve contains a finite family
which generates a covering sieve and whose image under `L` is an étale covering of schemes. -/
def IsEtaleCofinal (J : GrothendieckTopology C) : Prop :=
  ∀ (U : C) (S : Sieve U), S ∈ J U → ∃ E : PreZeroHypercover.{0} U, Finite E.I₀ ∧
    (E.map L).presieve₀ ∈ Scheme.precoverage @Etale (L.obj U) ∧ E.sieve₀ ≤ S ∧ E.sieve₀ ∈ J U

variable {L}

/-- Étale coverings of schemes are flat coverings. -/
private theorem precoverage_etale_le_flat :
    Scheme.precoverage @Etale ≤ Scheme.precoverage @Flat :=
  Scheme.precoverage_mono fun _ _ f hf => by
    have : Etale f := hf
    infer_instance

/-- An étale cofinal topology is flatly cofinal. -/
theorem IsEtaleCofinal.isFlatCofinal {J : GrothendieckTopology C} (hJ : IsEtaleCofinal L J) :
    AffineSiteBaseChange.IsFlatCofinal L J := by
  intro U S hS
  obtain ⟨E, hfin, hE, hES, hEJ⟩ := hJ U S hS
  exact ⟨E, hfin, precoverage_etale_le_flat _ hE, hES, hEJ⟩

/-- Under an étale cofinal topology, every covering sieve is refined by a covering family of
morphisms lying over étale morphisms of schemes. -/
theorem IsEtaleCofinal.isRefinableBy {J : GrothendieckTopology C} (hJ : IsEtaleCofinal L J)
    ⦃U : C⦄ (S : Sieve U) (hS : S ∈ J U) : J.IsRefinableBy (etaleMorphisms.inverseImage L) S := by
  obtain ⟨E, -, hE, hES, hEJ⟩ := hJ U S hS
  refine ⟨E.presieve₀, fun _ f hf => hES f (Sieve.le_generate _ _ _ hf), ?_, hEJ⟩
  rintro _ _ ⟨i⟩
  exact ((Scheme.presieve₀_mem_precoverage_iff _).1 hE).2 i

/-- The objects `V ⟶ x` of the slice `C/x` whose image under `L` is an étale morphism of
schemes. -/
def etaleOver (L : C ⥤ Scheme.{u}) (x : C) : ObjectProperty (Over x) :=
  fun V => Etale (L.map V.hom)

/-- The morphisms of the slice `C/x` whose underlying morphism lies over an étale morphism of
schemes. -/
abbrev etaleMap (L : C ⥤ Scheme.{u}) (x : C) : MorphismProperty (Over x) :=
  (etaleMorphisms.inverseImage L).inverseImage (Over.forget x)

/-- **The small étale site of `x` inside the slice `C/x`**: the full subcategory of `C/x` on the
objects lying over an étale morphism of schemes. -/
abbrev EtaleSlice (L : C ⥤ Scheme.{u}) (x : C) := (etaleOver L x).FullSubcategory

/-- The underlying scheme of an object of the small étale site of `x`. -/
abbrev toScheme (L : C ⥤ Scheme.{u}) (x : C) : EtaleSlice L x ⥤ Scheme.{u} :=
  (etaleOver L x).ι ⋙ Over.forget x ⋙ L

variable {x : C}

/-- The objects lying over an étale morphism are closed under the morphisms lying over étale
morphisms: if `V ⟶ W` and `W ⟶ x` lie over étale morphisms, so does `V ⟶ x`. -/
theorem etaleOver_of_etaleMap ⦃V W : Over x⦄ (f : V ⟶ W) (hf : etaleMap L x f)
    (hW : etaleOver L x W) : etaleOver L x V := by
  have : Etale (L.map f.left) := hf
  have : Etale (L.map W.hom) := hW
  show Etale (L.map V.hom)
  rw [← Over.w f, L.map_comp]
  infer_instance

/-- **Every morphism of the small étale site lies over an étale morphism of schemes**: a morphism
of schemes étale over `L x` between schemes étale over `L x` is étale. -/
@[sga "4 VII 1.2" "more general"]
theorem etaleMap_ι_map ⦃V W : EtaleSlice L x⦄ (f : V ⟶ W) :
    etaleMap L x ((etaleOver L x).ι.map f) := by
  have h : L.map V.obj.hom = L.map f.hom.left ≫ L.map W.obj.hom := by
    rw [← L.map_comp, Over.w f.hom]
  have : Etale (L.map W.obj.hom) := W.property
  have : Etale (L.map f.hom.left ≫ L.map W.obj.hom) := by rw [← h]; exact V.property
  exact Etale.of_comp (L.map f.hom.left) (L.map W.obj.hom)

/-- Every morphism of the small étale site lies over an étale morphism of schemes. -/
theorem etale_toScheme_map ⦃V W : EtaleSlice L x⦄ (f : V ⟶ W) :
    Etale ((toScheme L x).map f) :=
  etaleMap_ι_map f

variable (L x)

/-- The terminal object `id_x` of the small étale site of `x`. -/
abbrev terminal : EtaleSlice L x :=
  ⟨Over.mk (𝟙 x), show Etale (L.map (𝟙 x)) by rw [L.map_id]; infer_instance⟩

/-- `id_x` is a terminal object of the small étale site of `x`. -/
noncomputable def isTerminal : IsTerminal (terminal L x) :=
  IsTerminal.isTerminalOfObj (etaleOver L x).ι _ Over.mkIdTerminal

/-- The inclusion of the small étale site carries its terminal object to a terminal object of
the slice. -/
noncomputable def isTerminal_ι_obj : IsTerminal ((etaleOver L x).ι.obj (terminal L x)) :=
  Over.mkIdTerminal

section Pullbacks

variable {L x} [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan L]

/-- **The small étale site has fibre products, and its inclusion into the slice preserves
them.** Two morphisms of the small étale site with a common target have a fibre product there
which is also a fibre product in `C/x`. -/
theorem exists_isPullback ⦃U V W : EtaleSlice L x⦄ (g : V ⟶ U) (f : W ⟶ U) :
    ∃ (P : EtaleSlice L x) (a : P ⟶ V) (b : P ⟶ W),
      IsPullback a b g f ∧ IsPullback ((etaleOver L x).ι.map a) ((etaleOver L x).ι.map b)
        ((etaleOver L x).ι.map g) ((etaleOver L x).ι.map f) :=
  ObjectProperty.exists_isPullback_ι (fun _ _ _ _ _ _ ↦ inferInstance) etaleOver_of_etaleMap g f
    (etaleMap_ι_map g)

variable (L x) in
/-- The small étale site has fibre products. -/
instance hasPullbacks : HasPullbacks (EtaleSlice L x) :=
  @hasPullbacks_of_hasLimit_cospan _ _ fun {_ _ _} {g f} => by
    obtain ⟨P, a, b, h, -⟩ := exists_isPullback g f
    exact ⟨⟨⟨_, h.isLimit⟩⟩⟩

variable (L x) in
/-- The inclusion of the small étale site into the slice preserves fibre products. -/
instance preservesPullbacks_ι :
    PreservesLimitsOfShape WalkingCospan (etaleOver L x).ι := by
  refine ⟨fun {K} => ?_⟩
  have key : ∀ {U V W : EtaleSlice L x} (g : V ⟶ U) (f : W ⟶ U),
      PreservesLimit (cospan g f) (etaleOver L x).ι := by
    intro U V W g f
    obtain ⟨P, a, b, h, h'⟩ := exists_isPullback g f
    exact preservesLimit_of_preserves_limit_cone h.isLimit
      ((isLimitMapConePullbackConeEquiv (etaleOver L x).ι h.w).symm h'.isLimit)
  have := key (K.map WalkingCospan.Hom.inl) (K.map WalkingCospan.Hom.inr)
  exact preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm

variable (L x) in
/-- The underlying scheme functor of the small étale site preserves fibre products. -/
instance preservesPullbacks_toScheme : PreservesLimitsOfShape WalkingCospan (toScheme L x) := by
  unfold toScheme
  infer_instance

end Pullbacks

section Topology

/-- **The topology of the small étale site of `x`**: the topology it inherits from the slice
`(C/x, J_x)`, in which a family of morphisms covers exactly when its image covers in `C/x`. -/
abbrev topology (L : C ⥤ Scheme.{u}) (J : GrothendieckTopology C) (x : C) :
    GrothendieckTopology (EtaleSlice L x) :=
  (etaleOver L x).ι.inheritedTopology (J.over x)

variable {L} {J : GrothendieckTopology C} (hJ : IsEtaleCofinal L J)

include hJ

/-- Every covering sieve of the slice is refined by a covering family of morphisms lying over
étale morphisms. -/
theorem isRefinableBy_over ⦃V : Over x⦄ (T : Sieve V) (hT : T ∈ (J.over x) V) :
    (J.over x).IsRefinableBy (etaleMap L x) T :=
  GrothendieckTopology.isRefinableBy_over J (etaleMorphisms.inverseImage L) x hJ.isRefinableBy T hT

/-- The inclusion of the small étale site into the slice is cocontinuous. -/
theorem isCocontinuous_ι : (etaleOver L x).ι.IsCocontinuous (topology L J x) (J.over x) :=
  ObjectProperty.isCocontinuous_ι_inheritedTopology etaleOver_of_etaleMap (isRefinableBy_over x hJ)

/-- The inclusion of the small étale site into the slice is continuous. -/
theorem isContinuous_ι [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan L] :
    (etaleOver L x).ι.IsContinuous (topology L J x) (J.over x) :=
  ObjectProperty.isContinuous_ι_inheritedTopology (fun _ _ _ _ _ _ ↦ inferInstance)
    etaleOver_of_etaleMap (isRefinableBy_over x hJ)

/-- A finite family of morphisms of the small étale site covers as soon as its image covers the
slice. -/
theorem ofArrows_mem_topology {U : EtaleSlice L x} {I : Type*} (V : I → EtaleSlice L x)
    (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows (fun i => (V i).obj) (fun i => (etaleOver L x).ι.map (f i)) ∈
      (J.over x) U.obj) :
    Sieve.ofArrows V f ∈ topology L J x U := by
  show Sieve.ofArrows V f ∈ (etaleOver L x).ι.inheritedTopology (J.over x) U
  rw [← ObjectProperty.subcategoryCoverage_toGrothendieck etaleOver_of_etaleMap
    (isRefinableBy_over x hJ)]
  refine Coverage.Saturate.of U _ ⟨fun _ g ⟨i⟩ => etaleMap_ι_map (f i), ?_⟩
  rwa [Presieve.map_ofArrows]

/-- **The topology of the small étale site is flatly cofinal for its underlying scheme
functor.** -/
theorem isFlatCofinal [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan L] :
    AffineSiteBaseChange.IsFlatCofinal (toScheme L x) (topology L J x) := by
  have := isContinuous_ι x hJ
  intro U S hS
  have hS' : S.functorPushforward (etaleOver L x).ι ∈ (J.over x) U.obj :=
    (CoverPreserving.of_isContinuous (etaleOver L x).ι (topology L J x) (J.over x)).cover_preserve
      hS
  obtain ⟨E, hfin, hE, hES, hEJ⟩ :=
    hJ U.obj.left (Sieve.overEquiv U.obj (S.functorPushforward (etaleOver L x).ι)) hS'
  obtain ⟨hcov, het⟩ := (Scheme.presieve₀_mem_precoverage_iff _).1 hE
  let V : E.I₀ → EtaleSlice L x := fun i =>
    ⟨Over.mk (E.f i ≫ U.obj.hom), etaleOver_of_etaleMap (Over.homMk (E.f i) : Over.mk
      (E.f i ≫ U.obj.hom) ⟶ U.obj) (het i) U.property⟩
  let g : ∀ i, V i ⟶ U := fun i => ObjectProperty.homMk (Over.homMk (E.f i))
  let E' : PreZeroHypercover.{0} U := ⟨E.I₀, V, g⟩
  have hsieve : Sieve.ofArrows (fun i => (V i).obj) (fun i => (etaleOver L x).ι.map (g i)) ∈
      (J.over x) U.obj := by
    rw [GrothendieckTopology.mem_over_iff]
    refine J.superset_covering ?_ hEJ
    rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    rw [Sieve.overEquiv_iff]
    exact Sieve.ofArrows_mk _ _ i
  refine ⟨E', hfin, precoverage_etale_le_flat _ hE, ?_, ofArrows_mem_topology x hJ V g hsieve⟩
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    obtain ⟨W', a', b', ha', hab'⟩ :=
      (Sieve.overEquiv_iff _ _).1 (hES _ (Sieve.le_generate _ _ _ ⟨i⟩))
    have : g i = ObjectProperty.homMk (X := V i) b' ≫ a' :=
      (etaleOver L x).ι.map_injective (by rwa [Functor.map_comp])
    show S.arrows (g i)
    rw [this]
    exact S.downward_closed ha' _

end Topology

end Stacks.EtaleSlice
