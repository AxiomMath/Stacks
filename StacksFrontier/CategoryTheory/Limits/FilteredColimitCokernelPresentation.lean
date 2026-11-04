module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# A cokernel of a map between filtered colimits as a filtered colimit of cokernels

Let `H : I ⥤ E` and `G : J ⥤ E` be filtered diagrams with colimit cocones `cH` and `cG`, and
let `u : colim G ⟶ colim H`.  Suppose every `G j` is compact relative to `I`, meaning that
`Hom(G j, -)` commutes with colimits of shape `I`.  Then `cokernel u` is the filtered colimit of
the cokernels of the individual maps `α : G j ⟶ H i` which represent `u`.

The index category is the one of the source: triples `(i, j, α)` with
`α ≫ cH.ι.app i = cG.ι.app j ≫ u`, a morphism `(i, j, α) ⟶ (i', j', α')` being a pair
`φ : i ⟶ i'`, `ψ : j ⟶ j'` with `α ≫ H.map φ = G.map ψ ≫ α'`.  Compactness of the `G j` makes
this category filtered and makes both projections to `I` and to `J` final, so the two colimits
are computed over it and `u` becomes the colimit of the `α`.

## Main definitions

* `IsCompactDiagram`: the compactness hypothesis, that `Hom(G j, -)` commutes with colimits of
  the given shape.
* `cokernelDiagram` and `cokernelCocone`: the diagram of cokernels of the components of a
  natural transformation, and its cocone with point the cokernel of the induced map on the
  colimits.
* `Index`: the category of triples `(i, j, α)` above, with `toTarget` and `toSource` its
  projections to `I` and `J`, and `indexNatTrans` the natural transformation
  `G ∘ toSource ⟶ H ∘ toTarget` it carries.

## Main results

* `isColimitCokernelCocone`: cokernels commute with colimits — for a natural transformation of
  diagrams with colimit cocones, the cokernels of the components have colimit the cokernel of
  the induced map on the colimits.
* `exists_representative`: two triples with chosen common indices admit a single compatible
  representing map further along.
* `isFiltered_index`, `final_toTarget`, `final_toSource`: the category of triples is filtered
  and both projections are final.
* `isColimitIndexCokernelCocone` and `exists_isColimit_cokernel`: `cokernel u` is the colimit of
  `indexCokernelCocone`, and is a filtered colimit of cokernels of maps `G j ⟶ H i`.
* `exists_small_isColimit_cokernel`: the same over a small filtered index category, when `I` and
  `J` are small and `E` is locally small.

## Implementation notes

`E` is only assumed to have zero morphisms and cokernels; no additivity is used.  The source's
argument subtracts two maps `G j ⟶ H i` with the same image in `colim H` and pushes the
difference to zero further along, but the same conclusion follows from the injectivity half of
`Hom(G j, colim H) = colim Hom(G j, H i)` applied to the two maps directly, which needs no
subtraction.

`cokernelDiagram` is a `Functor`, so `(cokernelDiagram f).obj k` is not reducibly
`cokernel (f.app k)`; everything below is therefore phrased through `diagramπ` and
`diagramDesc`, whose types name the functor's value, rather than through `cokernel.π` and
`cokernel.desc` directly.

This is the formal second half of the proof of Stacks 07UW, where `E` is the category of
`𝒪_X`-modules on an algebraic space, the `G j` and `H i` are of finite presentation, the
compactness hypothesis is Stacks 07U7 and `cokernel u` is the module being presented.  The
statement here is pure category theory and carries no tag.

## References

* [Stacks Project, Tag 07UW](https://stacks.math.columbia.edu/tag/07UW)
* [Stacks Project, Tag 07U7](https://stacks.math.columbia.edu/tag/07U7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v₁ u₁ v₂ u₂

namespace Stacks.CategoryTheory.FilteredColimitCokernelPresentation

/-- `G` is a diagram of objects compact relative to the shape `I`: each `Hom(G j, -)` commutes
with colimits of shape `I`. -/
abbrev IsCompactDiagram (I : Type u₁) [Category.{v₁} I] {J : Type u₂} [Category.{v₂} J]
    {D : Type u} [Category.{v} D] (G : J ⥤ D) : Prop :=
  ∀ j : J, PreservesColimitsOfShape I (coyoneda.obj (op (G.obj j)))

variable {E : Type u} [Category.{v} E] [HasZeroMorphisms E] [HasCokernels E]

section Generic

variable {K : Type u₁} [Category.{v₁} K] {L N : K ⥤ E}

/-- The diagram of cokernels of the components of a natural transformation. -/
noncomputable def cokernelDiagram (f : L ⟶ N) : K ⥤ E where
  obj k := cokernel (f.app k)
  map h := cokernel.map _ _ (L.map h) (N.map h) (f.naturality h).symm
  map_id k := by
    apply coequalizer.hom_ext
    simp
  map_comp h h' := by
    apply coequalizer.hom_ext
    simp

/-- The projection onto the value of the cokernel diagram. -/
noncomputable def diagramπ (f : L ⟶ N) (k : K) : N.obj k ⟶ (cokernelDiagram f).obj k :=
  cokernel.π (f.app k)

/-- The projection onto the value of the cokernel diagram is an epimorphism. -/
instance epi_diagramπ (f : L ⟶ N) (k : K) : Epi (diagramπ f k) :=
  inferInstanceAs (Epi (cokernel.π (f.app k)))

/-- A component of `f` composed with the projection onto its cokernel is zero. -/
@[simp]
theorem comp_diagramπ (f : L ⟶ N) (k : K) : f.app k ≫ diagramπ f k = 0 :=
  cokernel.condition (f.app k)

/-- The map out of the value of the cokernel diagram induced by a map killing the component. -/
noncomputable def diagramDesc (f : L ⟶ N) {k : K} {Z : E} (t : N.obj k ⟶ Z)
    (ht : f.app k ≫ t = 0) : (cokernelDiagram f).obj k ⟶ Z :=
  cokernel.desc (f.app k) t ht

/-- The projection followed by the induced map out of the cokernel is the original map. -/
@[simp]
theorem diagramπ_comp_diagramDesc (f : L ⟶ N) {k : K} {Z : E} (t : N.obj k ⟶ Z)
    (ht : f.app k ≫ t = 0) : diagramπ f k ≫ diagramDesc f t ht = t :=
  cokernel.π_desc _ _ _

/-- Two maps out of a value of the cokernel diagram agree if they agree after the projection. -/
theorem diagram_hom_ext (f : L ⟶ N) {k : K} {Z : E} {a b : (cokernelDiagram f).obj k ⟶ Z}
    (h : diagramπ f k ≫ a = diagramπ f k ≫ b) : a = b :=
  (cancel_epi (diagramπ f k)).mp h

/-- The projections onto the values of the cokernel diagram are natural. -/
theorem diagramπ_comp_map (f : L ⟶ N) {k k' : K} (h : k ⟶ k') :
    diagramπ f k ≫ (cokernelDiagram f).map h = N.map h ≫ diagramπ f k' := by
  simp [diagramπ, cokernelDiagram]

variable {l : Cocone L} {n : Cocone N}

/-- The component of the cocone below: the map induced on cokernels by the leg `n.ι.app k`. -/
noncomputable def cokernelCoconeApp (f : L ⟶ N) (g : l.pt ⟶ n.pt)
    (hfg : ∀ k, l.ι.app k ≫ g = f.app k ≫ n.ι.app k) (k : K) :
    (cokernelDiagram f).obj k ⟶ cokernel g :=
  diagramDesc f (n.ι.app k ≫ cokernel.π g) (by
    rw [← Category.assoc, ← hfg k, Category.assoc, cokernel.condition, comp_zero])

/-- The projection followed by a component of the cokernel cocone is the leg `n.ι.app k`
followed by the projection onto `cokernel g`. -/
@[simp]
theorem diagramπ_comp_cokernelCoconeApp (f : L ⟶ N) (g : l.pt ⟶ n.pt)
    (hfg : ∀ k, l.ι.app k ≫ g = f.app k ≫ n.ι.app k) (k : K) :
    diagramπ f k ≫ cokernelCoconeApp f g hfg k = n.ι.app k ≫ cokernel.π g :=
  diagramπ_comp_diagramDesc _ _ _

/-- The components `cokernelCoconeApp` are compatible with the maps of the cokernel diagram. -/
theorem map_comp_cokernelCoconeApp (f : L ⟶ N) (g : l.pt ⟶ n.pt)
    (hfg : ∀ k, l.ι.app k ≫ g = f.app k ≫ n.ι.app k) {k k' : K} (h : k ⟶ k') :
    (cokernelDiagram f).map h ≫ cokernelCoconeApp f g hfg k' =
      cokernelCoconeApp f g hfg k := by
  apply diagram_hom_ext
  rw [← Category.assoc, diagramπ_comp_map, Category.assoc,
    diagramπ_comp_cokernelCoconeApp, diagramπ_comp_cokernelCoconeApp, ← Category.assoc,
    n.w h]

/-- The cocone on the diagram of cokernels whose point is the cokernel of the induced map on
the colimits. -/
noncomputable def cokernelCocone (f : L ⟶ N) (g : l.pt ⟶ n.pt)
    (hfg : ∀ k, l.ι.app k ≫ g = f.app k ≫ n.ι.app k) : Cocone (cokernelDiagram f) where
  pt := cokernel g
  ι :=
    { app := cokernelCoconeApp f g hfg
      naturality := fun {_ _} h =>
        (map_comp_cokernelCoconeApp f g hfg h).trans (Category.comp_id _).symm }

/-- The point of `cokernelCocone f g hfg` is `cokernel g`. -/
@[simp]
theorem cokernelCocone_pt (f : L ⟶ N) (g : l.pt ⟶ n.pt)
    (hfg : ∀ k, l.ι.app k ≫ g = f.app k ≫ n.ι.app k) :
    (cokernelCocone f g hfg).pt = cokernel g := rfl

/-- For a cocone `s` on the cokernel diagram, the composites `diagramπ f k ≫ s.ι.app k` are
compatible with the maps of `N`. -/
theorem map_comp_diagramπ_comp (f : L ⟶ N) (s : Cocone (cokernelDiagram f)) {k k' : K}
    (h : k ⟶ k') :
    N.map h ≫ diagramπ f k' ≫ s.ι.app k' = diagramπ f k ≫ s.ι.app k := by
  rw [← Category.assoc, ← diagramπ_comp_map, Category.assoc, s.w h]

/-- The cocone on the target diagram obtained from a cocone on the diagram of cokernels by
composing with the projections. -/
noncomputable def liftToTarget (f : L ⟶ N) (s : Cocone (cokernelDiagram f)) : Cocone N where
  pt := s.pt
  ι :=
    { app k := diagramπ f k ≫ s.ι.app k
      naturality := fun {_ _} h =>
        (map_comp_diagramπ_comp f s h).trans (Category.comp_id _).symm }

/-- The legs of `liftToTarget f s` are the projections followed by the legs of `s`. -/
@[simp]
theorem liftToTarget_ι_app (f : L ⟶ N) (s : Cocone (cokernelDiagram f)) (k : K) :
    (liftToTarget f s).ι.app k = diagramπ f k ≫ s.ι.app k := rfl

/-- The leg `n.ι.app k` followed by the map induced by `liftToTarget f s` is
`diagramπ f k ≫ s.ι.app k`. -/
theorem desc_liftToTarget_fac (f : L ⟶ N) {n : Cocone N} (hn : IsColimit n)
    (s : Cocone (cokernelDiagram f)) (k : K) :
    n.ι.app k ≫ hn.desc (liftToTarget f s) = diagramπ f k ≫ s.ι.app k :=
  (hn.fac (liftToTarget f s) k).trans (liftToTarget_ι_app f s k)

/-- Each component of `f` composed with the corresponding leg of `liftToTarget f s` is zero. -/
theorem comp_liftToTarget_ι_app (f : L ⟶ N) (s : Cocone (cokernelDiagram f)) (k : K) :
    f.app k ≫ (liftToTarget f s).ι.app k = 0 := by
  have h : (f.app k ≫ diagramπ f k) ≫ s.ι.app k = 0 := by rw [comp_diagramπ, zero_comp]
  exact (Category.assoc _ _ _).symm.trans h

/-- **Cokernels commute with colimits.**  For a natural transformation `f : L ⟶ N` of diagrams
with colimit cocones `l` and `n`, and `g : l.pt ⟶ n.pt` induced by `f`, the cokernels of the
components of `f` have colimit `cokernel g`. -/
noncomputable def isColimitCokernelCocone (f : L ⟶ N) (hl : IsColimit l) (hn : IsColimit n)
    (g : l.pt ⟶ n.pt) (hfg : ∀ k, l.ι.app k ≫ g = f.app k ≫ n.ι.app k) :
    IsColimit (cokernelCocone f g hfg) := by
  have kill (s : Cocone (cokernelDiagram f)) : g ≫ hn.desc (liftToTarget f s) = 0 := by
    apply hl.hom_ext
    intro k
    rw [← Category.assoc, hfg k, Category.assoc, hn.fac, comp_liftToTarget_ι_app, comp_zero]
  refine
    { desc := fun s => cokernel.desc g (hn.desc (liftToTarget f s)) (kill s)
      fac := fun s k => ?_
      uniq := fun s m hm => ?_ }
  · change cokernelCoconeApp f g hfg k ≫
      cokernel.desc g (hn.desc (liftToTarget f s)) (kill s) = s.ι.app k
    apply diagram_hom_ext
    have e : diagramπ f k ≫ cokernelCoconeApp f g hfg k ≫
        cokernel.desc g (hn.desc (liftToTarget f s)) (kill s) =
          n.ι.app k ≫ hn.desc (liftToTarget f s) := by
      rw [← Category.assoc, diagramπ_comp_cokernelCoconeApp, Category.assoc, cokernel.π_desc]
    exact e.trans (desc_liftToTarget_fac f hn s k)
  · have key : ∀ m' : cokernel g ⟶ s.pt,
        (∀ j : K, cokernelCoconeApp f g hfg j ≫ m' = s.ι.app j) →
          m' = cokernel.desc g (hn.desc (liftToTarget f s)) (kill s) := by
      intro m' hm'
      refine (cancel_epi (cokernel.π g)).mp (Eq.trans ?_ (cokernel.π_desc _ _ _).symm)
      apply hn.hom_ext
      intro k
      have e : n.ι.app k ≫ cokernel.π g ≫ m' = diagramπ f k ≫ s.ι.app k := by
        rw [← Category.assoc, ← diagramπ_comp_cokernelCoconeApp f g hfg k, Category.assoc,
          hm' k]
      exact e.trans (desc_liftToTarget_fac f hn s k).symm
    exact key m hm

end Generic

section Index

variable {I : Type u₁} [Category.{v₁} I] {J : Type u₂} [Category.{v₂} J]
  {H : I ⥤ E} {G : J ⥤ E} (cH : Cocone H) (cG : Cocone G) (u : cG.pt ⟶ cH.pt)

/-- A triple `(i, j, α)` of an object of `I`, an object of `J` and a map `α : G j ⟶ H i`
representing `u` on the nose. -/
structure Index where
  /-- The index in the target diagram. -/
  i : I
  /-- The index in the source diagram. -/
  j : J
  /-- The representing map. -/
  α : G.obj j ⟶ H.obj i
  /-- The map represents `u`. -/
  compat : α ≫ cH.ι.app i = cG.ι.app j ≫ u

/-- A morphism of triples: a pair of morphisms of indices making the square of representing
maps commute. -/
@[ext]
structure IndexHom (x y : Index cH cG u) where
  /-- The morphism in the target diagram. -/
  φ : x.i ⟶ y.i
  /-- The morphism in the source diagram. -/
  ψ : x.j ⟶ y.j
  /-- The square of representing maps commutes. -/
  w : x.α ≫ H.map φ = G.map ψ ≫ y.α

/-- The category of triples, with morphisms `IndexHom` composed componentwise. -/
instance : Category (Index cH cG u) where
  Hom x y := IndexHom cH cG u x y
  id x := { φ := 𝟙 x.i, ψ := 𝟙 x.j, w := by simp }
  comp {x y z} p q :=
    { φ := p.φ ≫ q.φ
      ψ := p.ψ ≫ q.ψ
      w := by
        rw [H.map_comp, G.map_comp, ← Category.assoc, p.w, Category.assoc, q.w,
          Category.assoc] }
  id_comp p := by ext <;> simp
  comp_id p := by ext <;> simp
  assoc p q r := by ext <;> simp

omit [HasZeroMorphisms E] [HasCokernels E] in
/-- Two morphisms of triples are equal if their components in `I` and in `J` are equal. -/
@[ext]
theorem Index.hom_ext {x y : Index cH cG u} {p q : x ⟶ y}
    (hφ : IndexHom.φ p = IndexHom.φ q) (hψ : IndexHom.ψ p = IndexHom.ψ q) : p = q :=
  IndexHom.ext hφ hψ

/-- The projection of the category of triples to the index category of the target diagram. -/
def toTarget : Index cH cG u ⥤ I where
  obj x := x.i
  map p := IndexHom.φ p

/-- The projection of the category of triples to the index category of the source diagram. -/
def toSource : Index cH cG u ⥤ J where
  obj x := x.j
  map p := IndexHom.ψ p

/-- The representing maps assemble into a natural transformation over the category of
triples. -/
def indexNatTrans : toSource cH cG u ⋙ G ⟶ toTarget cH cG u ⋙ H where
  app x := x.α
  naturality _ _ p := p.w.symm

omit [HasZeroMorphisms E] [HasCokernels E] in
/-- The component of `indexNatTrans` at a triple is its representing map. -/
@[simp]
theorem indexNatTrans_app (x : Index cH cG u) : (indexNatTrans cH cG u).app x = x.α := rfl

variable [IsFiltered I] [IsFiltered J]
variable {cH cG u}

omit [HasZeroMorphisms E] [HasCokernels E] [IsFiltered I] [IsFiltered J] in
/-- A map from `G j` into the colimit of `H` factors through one of the `H i`. -/
theorem exists_factor (hH : IsColimit cH) (hfp : IsCompactDiagram I G) (j : J)
    (x : G.obj j ⟶ cH.pt) : ∃ (i : I) (γ : G.obj j ⟶ H.obj i), γ ≫ cH.ι.app i = x := by
  have := hfp j
  obtain ⟨i, γ, hγ⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (coyoneda.obj (op (G.obj j))) hH) x
  exact ⟨i, γ, hγ⟩

omit [HasZeroMorphisms E] [HasCokernels E] [IsFiltered J] in
/-- Two maps from `G j` to the same `H i` with the same image in the colimit of `H` are
identified further along. -/
theorem exists_eq_of_comp_eq (hH : IsColimit cH) (hfp : IsCompactDiagram I G) {j : J} {i : I}
    (d d' : G.obj j ⟶ H.obj i) (h : d ≫ cH.ι.app i = d' ≫ cH.ι.app i) :
    ∃ (p : I) (φ : i ⟶ p), d ≫ H.map φ = d' ≫ H.map φ := by
  have := hfp j
  exact (Types.FilteredColimit.isColimit_eq_iff' (F := H ⋙ coyoneda.obj (op (G.obj j)))
    (isColimitOfPreserves (coyoneda.obj (op (G.obj j))) hH) d d').1 h

omit [HasZeroMorphisms E] [HasCokernels E] [IsFiltered J] in
/-- Two triples with a chosen common index in `I` and a chosen common index in `J` admit a single
representing map at a yet later index of `I`, compatible with both. -/
theorem exists_representative (hH : IsColimit cH) (hfp : IsCompactDiagram I G)
    (x y : Index cH cG u) {i₀ : I} {j₀ : J} (χx : x.i ⟶ i₀) (χy : y.i ⟶ i₀)
    (ψx : x.j ⟶ j₀) (ψy : y.j ⟶ j₀) :
    ∃ (p : I) (φ : i₀ ⟶ p) (α : G.obj j₀ ⟶ H.obj p),
      α ≫ cH.ι.app p = cG.ι.app j₀ ≫ u ∧
        x.α ≫ H.map (χx ≫ φ) = G.map ψx ≫ α ∧
          y.α ≫ H.map (χy ≫ φ) = G.map ψy ≫ α := by
  obtain ⟨m, γ, hγ⟩ := exists_factor hH hfp j₀ (cG.ι.app j₀ ≫ u)
  set ν : i₀ ⟶ IsFiltered.max i₀ m := IsFiltered.leftToMax i₀ m
  set μ : m ⟶ IsFiltered.max i₀ m := IsFiltered.rightToMax i₀ m
  have key : ∀ (z : Index cH cG u) (χ : z.i ⟶ i₀) (ψ : z.j ⟶ j₀) (q : I)
      (ρ : IsFiltered.max i₀ m ⟶ q),
      (z.α ≫ H.map (χ ≫ ν ≫ ρ)) ≫ cH.ι.app q =
        (G.map ψ ≫ γ ≫ H.map (μ ≫ ρ)) ≫ cH.ι.app q := by
    intro z χ ψ q ρ
    have hz : z.α ≫ H.map (χ ≫ ν ≫ ρ) ≫ cH.ι.app q = cG.ι.app z.j ≫ u := by
      rw [cH.w (χ ≫ ν ≫ ρ)]
      exact z.compat
    have hg : γ ≫ H.map (μ ≫ ρ) ≫ cH.ι.app q = cG.ι.app j₀ ≫ u := by
      rw [cH.w (μ ≫ ρ)]
      exact hγ
    rw [Category.assoc, hz, Category.assoc, Category.assoc, hg, ← Category.assoc, cG.w ψ]
  obtain ⟨p₁, φ₁, h₁⟩ := exists_eq_of_comp_eq hH hfp (x.α ≫ H.map (χx ≫ ν))
    (G.map ψx ≫ γ ≫ H.map μ) (by simpa using key x χx ψx _ (𝟙 _))
  obtain ⟨p₂, φ₂, h₂⟩ := exists_eq_of_comp_eq hH hfp (y.α ≫ H.map (χy ≫ ν ≫ φ₁))
    (G.map ψy ≫ γ ≫ H.map (μ ≫ φ₁)) (key y χy ψy p₁ φ₁)
  refine ⟨p₂, ν ≫ φ₁ ≫ φ₂, γ ≫ H.map (μ ≫ φ₁ ≫ φ₂), ?_, ?_, ?_⟩
  · rw [Category.assoc, cH.w (μ ≫ φ₁ ≫ φ₂)]
    exact hγ
  · have hx := congrArg (fun k : G.obj x.j ⟶ H.obj p₁ => k ≫ H.map φ₂) h₁
    simp only [Category.assoc, ← Functor.map_comp] at hx ⊢
    simpa using hx
  · simp only [Category.assoc, ← Functor.map_comp] at h₂ ⊢
    simpa using h₂

variable (cH cG u)

omit [HasZeroMorphisms E] [HasCokernels E] [IsFiltered I] in
/-- The category of triples is nonempty. -/
theorem nonempty_index (hH : IsColimit cH) (hfp : IsCompactDiagram I G) :
    Nonempty (Index cH cG u) := by
  obtain ⟨j⟩ := (IsFiltered.nonempty : Nonempty J)
  obtain ⟨i, γ, hγ⟩ := exists_factor hH hfp j (cG.ι.app j ≫ u)
  exact ⟨⟨i, j, γ, hγ⟩⟩

omit [HasZeroMorphisms E] [HasCokernels E] in
/-- The category of triples is filtered. -/
theorem isFiltered_index (hH : IsColimit cH) (hfp : IsCompactDiagram I G) :
    IsFiltered (Index cH cG u) := by
  refine { cocone_objs := ?_, cocone_maps := ?_, nonempty := nonempty_index cH cG u hH hfp }
  · intro x y
    obtain ⟨p, φ, α, hα, hx, hy⟩ := exists_representative hH hfp x y
      (IsFiltered.leftToMax x.i y.i) (IsFiltered.rightToMax x.i y.i)
      (IsFiltered.leftToMax x.j y.j) (IsFiltered.rightToMax x.j y.j)
    exact ⟨⟨p, _, α, hα⟩, ⟨_, _, hx⟩, ⟨_, _, hy⟩, trivial⟩
  · intro x y p q
    obtain ⟨c, φ, α, hα, h, -⟩ := exists_representative hH hfp y y
      (IsFiltered.coeqHom (IndexHom.φ p) (IndexHom.φ q))
      (IsFiltered.coeqHom (IndexHom.φ p) (IndexHom.φ q))
      (IsFiltered.coeqHom (IndexHom.ψ p) (IndexHom.ψ q))
      (IsFiltered.coeqHom (IndexHom.ψ p) (IndexHom.ψ q))
    refine ⟨⟨c, _, α, hα⟩,
      ⟨IsFiltered.coeqHom (IndexHom.φ p) (IndexHom.φ q) ≫ φ,
        IsFiltered.coeqHom (IndexHom.ψ p) (IndexHom.ψ q), h⟩, ?_⟩
    ext
    · show IndexHom.φ p ≫ IsFiltered.coeqHom (IndexHom.φ p) (IndexHom.φ q) ≫ φ =
        IndexHom.φ q ≫ IsFiltered.coeqHom (IndexHom.φ p) (IndexHom.φ q) ≫ φ
      rw [← Category.assoc, ← Category.assoc, IsFiltered.coeq_condition]
    · show IndexHom.ψ p ≫ IsFiltered.coeqHom (IndexHom.ψ p) (IndexHom.ψ q) =
        IndexHom.ψ q ≫ IsFiltered.coeqHom (IndexHom.ψ p) (IndexHom.ψ q)
      rw [IsFiltered.coeq_condition]

omit [HasZeroMorphisms E] [HasCokernels E] in
/-- The projection to the index category of the target diagram is final. -/
theorem final_toTarget (hH : IsColimit cH) (hfp : IsCompactDiagram I G) :
    (toTarget cH cG u).Final := by
  have := isFiltered_index cH cG u hH hfp
  obtain ⟨w⟩ := nonempty_index cH cG u hH hfp
  refine Functor.final_of_exists_of_isFiltered _ (fun i => ?_) (fun {i x} s s' => ?_)
  · obtain ⟨p, φ, α, hα, -, -⟩ := exists_representative hH hfp w w
      (IsFiltered.rightToMax i w.i) (IsFiltered.rightToMax i w.i) (𝟙 w.j) (𝟙 w.j)
    exact ⟨⟨p, _, α, hα⟩, ⟨IsFiltered.leftToMax i w.i ≫ φ⟩⟩
  · obtain ⟨c, φ, α, hα, h, -⟩ := exists_representative hH hfp x x
      (IsFiltered.coeqHom s s') (IsFiltered.coeqHom s s') (𝟙 x.j) (𝟙 x.j)
    refine ⟨⟨c, _, α, hα⟩, ⟨IsFiltered.coeqHom s s' ≫ φ, 𝟙 x.j, h⟩, ?_⟩
    show s ≫ IsFiltered.coeqHom s s' ≫ φ = s' ≫ IsFiltered.coeqHom s s' ≫ φ
    rw [← Category.assoc, ← Category.assoc, IsFiltered.coeq_condition]

omit [HasZeroMorphisms E] [HasCokernels E] in
/-- The projection to the index category of the source diagram is final. -/
theorem final_toSource (hH : IsColimit cH) (hfp : IsCompactDiagram I G) :
    (toSource cH cG u).Final := by
  have := isFiltered_index cH cG u hH hfp
  refine Functor.final_of_exists_of_isFiltered _ (fun j => ?_) (fun {j x} s s' => ?_)
  · obtain ⟨i, γ, hγ⟩ := exists_factor hH hfp j (cG.ι.app j ≫ u)
    exact ⟨⟨i, j, γ, hγ⟩, ⟨𝟙 j⟩⟩
  · obtain ⟨c, φ, α, hα, h, -⟩ := exists_representative hH hfp x x (𝟙 x.i) (𝟙 x.i)
      (IsFiltered.coeqHom s s') (IsFiltered.coeqHom s s')
    refine ⟨⟨c, _, α, hα⟩, ⟨𝟙 x.i ≫ φ, IsFiltered.coeqHom s s', h⟩, ?_⟩
    show s ≫ IsFiltered.coeqHom s s' = s' ≫ IsFiltered.coeqHom s s'
    rw [IsFiltered.coeq_condition]

omit [HasZeroMorphisms E] [HasCokernels E] [IsFiltered I] [IsFiltered J] in
/-- The representing maps are compatible with the whiskered colimit cocones. -/
theorem whisker_fac (x : Index cH cG u) :
    (cG.whisker (toSource cH cG u)).ι.app x ≫ u =
      (indexNatTrans cH cG u).app x ≫ (cH.whisker (toTarget cH cG u)).ι.app x :=
  x.compat.symm

/-- The cocone of the cokernels of the representing maps, with point `cokernel u`. -/
noncomputable def indexCokernelCocone : Cocone (cokernelDiagram (indexNatTrans cH cG u)) :=
  cokernelCocone (l := cG.whisker (toSource cH cG u)) (n := cH.whisker (toTarget cH cG u))
    (indexNatTrans cH cG u) u (whisker_fac cH cG u)

omit [IsFiltered I] [IsFiltered J] in
/-- The point of `indexCokernelCocone` is `cokernel u`. -/
@[simp]
theorem indexCokernelCocone_pt : (indexCokernelCocone cH cG u).pt = cokernel u := rfl

/-- **The cokernel of `u` is the colimit of the cokernels of its representatives.** -/
noncomputable def isColimitIndexCokernelCocone (hH : IsColimit cH) (hG : IsColimit cG)
    (hfp : IsCompactDiagram I G) : IsColimit (indexCokernelCocone cH cG u) :=
  have := isFiltered_index cH cG u hH hfp
  have := final_toTarget cH cG u hH hfp
  have := final_toSource cH cG u hH hfp
  isColimitCokernelCocone _
    ((Functor.Final.isColimitWhiskerEquiv (toSource cH cG u) cG).symm hG)
    ((Functor.Final.isColimitWhiskerEquiv (toTarget cH cG u) cH).symm hH) u _

/-- **A cokernel of a map between filtered colimits of compact objects is a filtered colimit of
cokernels of maps between the objects themselves.** -/
theorem exists_isColimit_cokernel (hH : IsColimit cH) (hG : IsColimit cG)
    (hfp : IsCompactDiagram I G) :
    ∃ (K : Type (max u₁ u₂ v)) (_ : Category.{max v₁ v₂} K) (_ : IsFiltered K)
      (D : K ⥤ E) (c : Cocone D), c.pt = cokernel u ∧ Nonempty (IsColimit c) ∧
        ∀ k, ∃ (j : J) (i : I) (α : G.obj j ⟶ H.obj i),
          α ≫ cH.ι.app i = cG.ι.app j ≫ u ∧ D.obj k = cokernel α :=
  ⟨Index cH cG u, inferInstance, isFiltered_index cH cG u hH hfp,
    cokernelDiagram (indexNatTrans cH cG u), indexCokernelCocone cH cG u, rfl,
    ⟨isColimitIndexCokernelCocone cH cG u hH hG hfp⟩,
    fun x => ⟨x.j, x.i, x.α, x.compat, rfl⟩⟩

/-- **The cokernel of a map between two filtered colimits, as a filtered colimit over a small
index.**  When `I` and `J` are small and `E` is locally small, `cokernel u` is a colimit over a
small filtered category of cokernels of maps `α : G j ⟶ H i` representing `u`. -/
theorem exists_small_isColimit_cokernel {I J : Type v₁} [SmallCategory I] [SmallCategory J]
    [IsFiltered I] [IsFiltered J] {H : I ⥤ E} {G : J ⥤ E} (cH : Cocone H) (cG : Cocone G)
    (u : cG.pt ⟶ cH.pt) [LocallySmall.{v₁} E] (hH : IsColimit cH) (hG : IsColimit cG)
    (hfp : IsCompactDiagram I G) :
    ∃ (K : Type v₁) (_ : SmallCategory K) (_ : IsFiltered K)
      (D : K ⥤ E) (c : Cocone D), c.pt = cokernel u ∧ Nonempty (IsColimit c) ∧
        ∀ k, ∃ (j : J) (i : I) (α : G.obj j ⟶ H.obj i),
          α ≫ cH.ι.app i = cG.ι.app j ≫ u ∧ D.obj k = cokernel α := by
  have : Small.{v₁} (Index cH cG u) := by
    let P : (Σ (i : I) (j : J), (G.obj j ⟶ H.obj i)) → Prop :=
      fun p => p.2.2 ≫ cH.ι.app p.1 = cG.ι.app p.2.1 ≫ u
    refine small_of_surjective (f := fun p : Subtype P =>
      (⟨p.1.1, p.1.2.1, p.1.2.2, p.2⟩ : Index cH cG u)) ?_
    rintro ⟨i, j, α, h⟩
    exact ⟨⟨⟨i, j, α⟩, h⟩, rfl⟩
  have : EssentiallySmall.{v₁} (Index cH cG u) :=
    essentiallySmall_of_small_of_locallySmall _
  have hfil : IsFiltered (Index cH cG u) := isFiltered_index cH cG u hH hfp
  let e := equivSmallModel.{v₁} (Index cH cG u)
  refine ⟨SmallModel.{v₁} (Index cH cG u), inferInstance, IsFiltered.of_equivalence e,
    e.inverse ⋙ cokernelDiagram (indexNatTrans cH cG u),
    (indexCokernelCocone cH cG u).whisker e.inverse, rfl,
    ⟨(isColimitIndexCokernelCocone cH cG u hH hG hfp).whiskerEquivalence e.symm⟩,
    fun x => ⟨(e.inverse.obj x).j, (e.inverse.obj x).i, (e.inverse.obj x).α,
      (e.inverse.obj x).compat, rfl⟩⟩

end Index

end Stacks.CategoryTheory.FilteredColimitCokernelPresentation

end
